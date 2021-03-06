/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    theory_wmaxsat.h

Abstract:

    Weighted Max-SAT theory plugin.

Author:

    Nikolaj Bjorner (nbjorner) 2013-11-05

Notes:

--*/

#ifndef _THEORY_WMAXSAT_H_
#define _THEORY_WMAXSAT_H_

#include "smt_theory.h"
#include "smt_clause.h"
#include "filter_model_converter.h"

namespace smt {
    class theory_wmaxsat : public theory {
        struct stats {
            unsigned m_num_blocks;
            void reset() { memset(this, 0, sizeof(*this)); }
            stats() { reset(); }
        };        
        filter_model_converter&     m_mc;
        mutable unsynch_mpz_manager m_mpz;
        app_ref_vector           m_vars;        // Auxiliary variables per soft clause
        expr_ref_vector          m_fmls;        // Formulas per soft clause
        vector<rational>         m_rweights;    // weights of theory variables.
        scoped_mpz_vector        m_zweights;
        scoped_mpz_vector        m_old_values;
        svector<theory_var>      m_costs;       // set of asserted theory variables
        svector<theory_var>      m_cost_save;   // set of asserted theory variables
        rational                 m_rcost;       // current sum of asserted costs
        rational                 m_rmin_cost;   // current maximal cost assignment.
        scoped_mpz               m_zcost;       // current sum of asserted costs
        scoped_mpz               m_zmin_cost;   // current maximal cost assignment.
        bool                     m_found_optimal; 
        u_map<theory_var>        m_bool2var;    // bool_var -> theory_var
        svector<bool_var>        m_var2bool;    // theory_var -> bool_var
        bool                     m_propagate;  
        bool                     m_normalize; 
        rational                 m_den;         // lcm of denominators for rational weights.
        svector<bool>            m_assigned;
        stats                    m_stats;
    public:
        theory_wmaxsat(ast_manager& m, filter_model_converter& mc);
        virtual ~theory_wmaxsat();
        void get_assignment(svector<bool>& result);
        virtual void init_search_eh();
        bool_var assert_weighted(expr* fml, rational const& w);
        bool_var register_var(app* var, bool attach);
        rational const& get_min_cost();
        class numeral_trail : public trail<context> {
            typedef scoped_mpz T;
            T & m_value;
            scoped_mpz_vector&  m_old_values;            
        public:
            numeral_trail(T & value, scoped_mpz_vector& old):
                m_value(value),
                m_old_values(old) {
                old.push_back(value);
            }
            
            virtual ~numeral_trail() {
            }
            
            virtual void undo(context & ctx) {
                m_value = m_old_values.back();
                m_old_values.shrink(m_old_values.size() - 1);
            }
        };
        virtual void assign_eh(bool_var v, bool is_true);
        virtual final_check_status final_check_eh();
        virtual bool use_diseqs() const { 
            return false;
        }
        virtual bool build_models() const { 
            return false;
        }
        void reset_local();
        virtual void reset_eh();
        virtual theory * mk_fresh(context * new_ctx) { return 0; }
        virtual bool internalize_atom(app * atom, bool gate_ctx) { return false; }
        virtual bool internalize_term(app * term) { return false; }
        virtual void new_eq_eh(theory_var v1, theory_var v2) { }
        virtual void new_diseq_eh(theory_var v1, theory_var v2) { }

        virtual void collect_statistics(::statistics & st) const {
            st.update("wmaxsat num blocks", m_stats.m_num_blocks);
        }
        virtual bool can_propagate() {
            return m_propagate;
        }

        virtual void propagate();
        bool is_optimal() const;
        expr_ref mk_block();

        expr_ref mk_optimal_block(svector<bool_var> const& ws, rational const& weight);
    private:

        void block();
        void normalize();
       
        class compare_cost {
            theory_wmaxsat& m_th;
        public:
            compare_cost(theory_wmaxsat& t):m_th(t) {}
            bool operator() (theory_var v, theory_var w) const { 
                return m_th.m_mpz.gt(m_th.m_zweights[v], m_th.m_zweights[w]); 
            }
        };


    };
};

#endif
