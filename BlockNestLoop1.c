static TupleTableSlot *
ExecBlockNestLoop(PlanState *pstate)
{
    int BSize = 2;
	NestLoopState *node = castNode(NestLoopState, pstate);
	NestLoop   *nl;
	PlanState  *innerPlan;
	PlanState  *outerPlan;
	TupleTableSlot *outerTupleSlot;
	TupleTableSlot *innerTupleSlot;
	ExprState  *joinqual;
	ExprState  *otherqual;
	ExprContext *econtext;
	ListCell   *lc;

    TupleTableSlot *TTSBlock[2]; //TupleTable
	TupleTableSlot *outerTupleSlot0;
	EState *estate;
    TupleDesc tuptype;
	
    estate = node->js.ps.state;
    //tuptype = node->js.ps.scandesc;
    tuptype = pstate->scandesc;

	//InitTupleTableBlock(estate,tuptype,TTSBlock);
    for(int i=0;i<BSize;i++){
        TTSBlock[i] = ExecInitNullTupleSlot(estate, tuptype);
    }
    int cursor = 0;
    int upper = 0;


	CHECK_FOR_INTERRUPTS();

	/*
	 * get information from the node
	 */
	ENL1_printf("getting info from node");

	nl = (NestLoop *) node->js.ps.plan;
	joinqual = node->js.joinqual;
	otherqual = node->js.ps.qual;
	outerPlan = outerPlanState(node);
	innerPlan = innerPlanState(node);
	econtext = node->js.ps.ps_ExprContext;

    outerTupleSlot0 = TTSBlock[0];

	/*
	 * Reset per-tuple memory context to free any expression evaluation
	 * storage allocated in the previous tuple cycle.
	 */
	ResetExprContext(econtext);

	/*
	 * Ok, everything is setup for the join so now loop until we return a
	 * qualifying join tuple.
	 */
	ENL1_printf("entering main loop");

	for (;;)
	{
		/*
		 * If we don't have an outer tuple, get the next one and reset the
		 * inner scan.
		 */
		if (node->nl_NeedNewOuter)
		{
			ENL1_printf("getting new outer tuple");
            upper = 0;
            cursor = 0;
            for(int i=0; i<BSize; i++){
                outerTupleSlot = ExecProcNode(outerPlan);
                if(TupIsNull(outerTupleSlot)){
                    break;
                }
                else{
                    ExecCopySlot(TTSBlock[i], outerTupleSlot);
                    upper += 1;
                }

            }

			outerTupleSlot0 = TTSBlock[0];

			/*
			 * if there are no more outer tuples, then the join is complete..
			 */
			if (upper == 0)
			{
				ENL1_printf("no outer tuple, ending join");
				return NULL;
			}

			ENL1_printf("saving new outer tuple information");
			econtext->ecxt_outertuple = outerTupleSlot0;
			node->nl_NeedNewOuter = false;
			node->nl_MatchedOuter = false;

			/*
			 * fetch the values of any outer Vars that must be passed to the
			 * inner scan, and store them in the appropriate PARAM_EXEC slots.
			 */  //cck确定join的各种参数，比如在什么属性上join等等 
			foreach(lc, nl->nestParams)
			{
				NestLoopParam *nlp = (NestLoopParam *) lfirst(lc);
				int			paramno = nlp->paramno;
				ParamExecData *prm;

				prm = &(econtext->ecxt_param_exec_vals[paramno]);
				/* Param value should be an OUTER_VAR var */
				Assert(IsA(nlp->paramval, Var));
				Assert(nlp->paramval->varno == OUTER_VAR);
				Assert(nlp->paramval->varattno > 0);
				prm->value = slot_getattr(outerTupleSlot,
										  nlp->paramval->varattno,
										  &(prm->isnull));
				/* Flag parameter value as changed */
				innerPlan->chgParam = bms_add_member(innerPlan->chgParam,
													 paramno);
			}

			/*
			 * now rescan the inner plan
			 */
			ENL1_printf("rescanning inner plan");
			ExecReScan(innerPlan);
		}

		/*
		 * we have an outerTuple, try to get the next inner tuple.
		 */
		ENL1_printf("getting new inner tuple");

		innerTupleSlot = ExecProcNode(innerPlan);//cck 加载一条内关系元组
		econtext->ecxt_innertuple = innerTupleSlot;//放到econtext中，他是一个ExprContext类型的数据结构

		if (TupIsNull(innerTupleSlot))
		{
			ENL1_printf("no inner tuple, need new outer tuple");

			node->nl_NeedNewOuter = true;

			if (!node->nl_MatchedOuter &&
				(node->js.jointype == JOIN_LEFT ||
				 node->js.jointype == JOIN_ANTI))
			{
				/*
				 * We are doing an outer join and there were no join matches
				 * for this outer tuple.  Generate a fake join tuple with
				 * nulls for the inner tuple, and return it if it passes the
				 * non-join quals.
				 */ //CCK 这里是在考虑join 的不同方式产生的不同，比如LeftJoin的时候，如果没匹配远足，右边的属性需要用null填补。
				econtext->ecxt_innertuple = node->nl_NullInnerTupleSlot;

				ENL1_printf("testing qualification for outer-join tuple");

                for(int i=0;i<upper;i++){
                    econtext->ecxt_outertuple = TTSBlock[i];
                    if (otherqual == NULL || ExecQual(otherqual, econtext))
				    {// CCK 不是很明白otherqual的作用，似乎是标记Outer已经没有未匹配的元组了，下面就直接返回了
					    /*
					     * qualification was satisfied so we project and return
					     * the slot containing the result tuple using
					     * ExecProject().
					     */ //CCK 使用ExecProject输出整个join过程的结果（满足条件的元组们在ProjInfo中）
					    ENL1_printf("qualification succeeded, projecting tuple");

					    return ExecProject(node->js.ps.ps_ProjInfo);
				    }
				    else
					    InstrCountFiltered2(node, 1); //CCK 似乎是filter移动移位1位的意思 --匹配
                }
				
			}

			/*
			 * Otherwise just return to top of loop for a new outer tuple.
			 */
			continue;
		}
        /*
		 * at this point we have a new pair of inner and outer tuples so we
		 * test the inner and outer tuples to see if they satisfy the node's
		 * qualification.
		 *
		 * Only the joinquals determine MatchedOuter status, but all quals
		 * must pass to actually return the tuple. 
		 * //CCK 虽然只有用于join的quals（qualifications）才对Match有影响，但所有的quals都要输出给return——tuples
		 */
        for(int i=0; i<upper; i++){
            ENL1_printf("testing qualification");
            econtext->ecxt_outertuple = TTSBlock[i];
            if (ExecQual(joinqual, econtext)) //CCK 不管怎么做的，反正就是确定join条件满不满足
	    	{
    			node->nl_MatchedOuter = true;

    			/* In an antijoin, we never return a matched tuple */
    			//CCK　奇怪的antiJoin 不返回元组
    			if (node->js.jointype == JOIN_ANTI)
    			{
    				node->nl_NeedNewOuter = true;
    				break;		/* return to top of loop */
    			}

			/*
			 * If we only need to join to the first matching inner tuple, then
			 * consider returning this one, but after that continue with next
			 * outer tuple.
			 */
    			/*if (node->js.single_match) //CCK 比如外键，这个信息应该在PlanState中有存储
    				node->nl_NeedNewOuter = true;*/ //待处理CKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKK

    			if (otherqual == NULL || ExecQual(otherqual, econtext))
		    	{
	    			/*
	    			 * qualification was satisfied so we project and return the
    				 * slot containing the result tuple using ExecProject().
				     */
				    //CCK ProjInfo中全是slots
				    ENL1_printf("qualification succeeded, projecting tuple");

				    return ExecProject(node->js.ps.ps_ProjInfo);
			    }
			    else
		    		InstrCountFiltered2(node, 1); //CCK 匹配的移动1位
		    }
		    else
			    InstrCountFiltered1(node, 1); //CCK 不匹配的移动1位

		    /*
		     * Tuple fails qual, so free per-tuple memory and try again.
		     */
		    ResetExprContext(econtext); //CCK 清楚本次JoinCheck的数据

		    ENL1_printf("qualification failed, looping"); //CCK 本次匹配失败，继续循环
        }
	}
}
