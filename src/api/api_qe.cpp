#include <iostream>
#include "z3.h"
#include "api_log_macros.h"
#include "api_context.h"
#include "api_util.h"
#include "api_model.h"
#include "api_ast_map.h"
#include "api_ast_vector.h"

#include "qe_util.h"
#include "qe_lite.h"
#include "spacer_util.h"

#include "expr_map.h"

extern "C" 
{
  Z3_ast Z3_API Z3_qe_model_project (Z3_context c, 
                                     Z3_model m, 
                                     unsigned num_bounds, 
                                     Z3_app const bound[],
                                     Z3_ast body)
  {
    Z3_TRY;
    LOG_Z3_qe_model_project (c, m, num_bounds, bound, body);
    RESET_ERROR_CODE();

    app_ref_vector vars(mk_c(c)->m ());
    for (unsigned i = 0; i < num_bounds; ++i) 
    {
      app *a = to_app (bound [i]);
      if (a->get_kind () != AST_APP)
      {
        SET_ERROR_CODE (Z3_INVALID_ARG);
        RETURN_Z3(0);
      }
      vars.push_back (a);
    }
    
    expr_ref result (mk_c(c)->m ());
    result = to_expr (body);
    model_ref model (to_model_ref (m));
    spacer::qe_project (mk_c(c)->m (), vars, result, model);
    mk_c(c)->save_ast_trail (result.get ());
    
    return of_expr (result.get ());
    Z3_CATCH_RETURN(0);
  }
  
  Z3_ast Z3_API Z3_qe_model_project_skolem (Z3_context c,
                                       Z3_model m,
                                       unsigned num_bounds,
                                       Z3_app const bound[],
                                       Z3_ast body,
                                       Z3_ast_map map)
    {
      Z3_TRY;
      LOG_Z3_qe_model_project_skolem (c, m, num_bounds, bound, body, map);
      RESET_ERROR_CODE();

      ast_manager& man = mk_c(c)->m ();
      app_ref_vector vars(man);
      for (unsigned i = 0; i < num_bounds; ++i)
      {
        app *a = to_app (bound [i]);
        if (a->get_kind () != AST_APP)
        {
          SET_ERROR_CODE (Z3_INVALID_ARG);
          RETURN_Z3(0);
        }
        vars.push_back (a);
      }

      expr_ref result (mk_c(c)->m ());
      result = to_expr (body);
      model_ref model (to_model_ref (m));
      expr_map emap (man);

      spacer::qe_project (mk_c(c)->m (), vars, result, model, emap);
      mk_c(c)->save_ast_trail (result.get ());

      obj_map<ast, ast*> &map_z3 = to_ast_map_ref(map);

      for (expr_map::iterator it = emap.begin(), end = emap.end(); it != end; ++it){
        man.inc_ref(&(it->get_key()));
        man.inc_ref(it->get_value());
        map_z3.insert(&(it->get_key()), it->get_value());
      }

      return of_expr (result.get ());
      Z3_CATCH_RETURN(0);
    }

  Z3_ast Z3_API Z3_model_extrapolate (Z3_context c,
                                      Z3_model m, 
                                      Z3_ast fml)
  {
    Z3_TRY;
    LOG_Z3_model_extrapolate (c, m, fml);
    RESET_ERROR_CODE();
    
    model_ref model (to_model_ref (m));
    expr_ref_vector facts (mk_c(c)->m ());
    facts.push_back (to_expr (fml));
    qe::flatten_and (facts);
    
    spacer::model_evaluator mev (mk_c(c)->m());
    mev.reset (model);
    
    expr_ref_vector lits (mk_c(c)->m());
    spacer::compute_implicant_literals (mev, facts, lits);
    
    expr_ref result (mk_c(c)->m ());
    result = qe::mk_and (lits);
    mk_c(c)->save_ast_trail (result.get ());
    
    return of_expr (result.get ());
    Z3_CATCH_RETURN(0);
  }

  Z3_ast Z3_API Z3_qe_lite (Z3_context c, Z3_ast_vector vars, Z3_ast body)
  {
    Z3_TRY;
    LOG_Z3_qe_lite (c, vars, body);
    RESET_ERROR_CODE();
    ast_ref_vector &vVars = to_ast_vector_ref (vars);
    
    app_ref_vector vApps (mk_c(c)->m());
    for (unsigned i = 0; i < vVars.size (); ++i)
    {
      app *a = to_app (vVars.get (i));
      if (a->get_kind () != AST_APP)
      {
        SET_ERROR_CODE (Z3_INVALID_ARG);
        RETURN_Z3(0);
      }
      vApps.push_back (a);
    }
        
    expr_ref result (mk_c(c)->m ());
    result = to_expr (body);
    
    qe_lite qe (mk_c(c)->m ());
    qe (vApps, result);

    // -- copy back variables that were not eliminated
    if (vApps.size () < vVars.size ())
    {
      vVars.reset ();
      for (unsigned i = 0; i < vApps.size (); ++i)
        vVars.push_back (vApps.get (i));
    }
    
    mk_c(c)->save_ast_trail (result.get ());
    return of_expr (result);
    Z3_CATCH_RETURN(0);
  }
  
}
