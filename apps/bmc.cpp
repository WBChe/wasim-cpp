#include <chrono>
#include "assert.h"
#include "config/testpath.h"
#include "frontend/btor2_encoder.h"
#include "framework/symsim.h"
#include "framework/ts.h"
#include "smt-switch/boolector_factory.h"

using namespace wasim;
using namespace smt;

bool check_prop(const Term & p, const TermVec & asmpt, SmtSolver & solver) {
  solver->push();
  for (const auto & a : asmpt) {
    solver->assert_formula(a);
  }
  solver->assert_formula(solver->make_term(Not, p));
  auto res = solver->check_sat();
  solver->pop();
  return res.is_unsat();
}

static Term and_vec(const TermVec & v, SmtSolver & solver) {
  if (v.empty())
    return solver->make_term(true);
  if (v.size() == 1)
    return v.at(0);
    
  auto ret = v.at(0);
  for (size_t idx = 1; idx < v.size() ; ++idx)
    ret = solver->make_term(smt::And, ret, v.at(idx));
  return ret;
}

int main(int argc, char ** argv) {

  if (argc < 3) {
    std::cout << "[Usage] " << argv[0] << " btor bound" << std::endl;
    return 1;
  }

  std::string btor_fname = argv[1];
  unsigned bound = atoi(argv[2]);
  
  SmtSolver solver = BoolectorSolverFactory::create(false);

  solver->set_logic("QF_UFBV");
  solver->set_opt("incremental", "true");
  solver->set_opt("produce-models", "true");
  solver->set_opt("produce-unsat-assumptions", "true");

  TransitionSystem sts(solver);
  BTOR2Encoder btor_parser(btor_fname, sts);

  const auto & propvec = sts.prop();
  if (propvec.empty()) {
    std::cout << "No property to check!" << std::endl;
    return 1;
  }

  auto prop = and_vec(propvec, solver);

  /*------------------------------simulation--------------------------------*/

  SymbolicSimulator sim(sts, solver);
  sim.init();
  // check init condition
  if (! check_prop(
    sim.interpret_state_expr_on_curr_frame(prop, false),
    sim.all_assumptions(),
    solver )) {
    std::cout << "[bmc] failed at init!" << std::endl;
    return 2;
  }

  for (unsigned i = 1; i<=bound; ++i) {
    sim.sim_one_step();
    if (check_prop(
      sim.interpret_state_expr_on_curr_frame(prop, false),
      sim.all_assumptions(),
      solver )) {
      std::cout << "[bmc] bound " << i << " passed." << std::endl;
    } else {
      std::cout << "[bmc] failed at bound " << i << std::endl;
      return 2;
    }
  }
  std::cout << "[bmc] bound " << bound << " is reached. No bounded CEX bound." << std::endl;

  return 0;
}


