import Langlands.Automorphic.Unramified.CyclicWeakInductionGammaFromEquations
import Langlands.Automorphic.Unramified.WeakInductionOrbitRestriction

/-! # Unique-place supercuspidality from equal-rank pair equations -/

universe uF uE uV uW

set_option autoImplicit false

namespace Langlands.Automorphic.Unramified

open Langlands.Global
open Langlands.Global.CuspidalPairFunctionalEquation Langlands.Global.RankinSelbergGlobal

private theorem supercuspidality_of_twistEquations
    (hF : EqualRankTwistEngineInputsStatement.{uF,uV})
    (hE : EqualRankTwistEngineInputsStatement.{uE,uW}) :
    CyclicWeakInductionSupercuspidalStatement.{uF,uE,uV,uW} ∧
      CyclicWeakInductionSupercuspidalTCStatement.{uF,uE,uV,uW} := by
  have hG := cyclicWeakInductionGammaOrderFromTwistEquations hF hE weakInductionOrbitBaseChange
  exact ⟨cyclicWeakInductionSupercuspidal_of_gammaOrder hG,
    cyclicWeakInductionSupercuspidalTC_of_gammaOrder hG⟩

/-- The completed Rankin–Selberg equation in the two field and presentation
universes suffices for both cyclic weak-induction supercuspidality statements. -/
def CyclicWeakInductionSupercuspidalFromPairEquationsStatement : Prop :=
  CuspidalPairGlobalFunctionalEquationStatement.{uF,uV} →
  CuspidalPairGlobalFunctionalEquationStatement.{uE,uW} →
  CyclicWeakInductionSupercuspidalStatement.{uF,uE,uV,uW} ∧
    CyclicWeakInductionSupercuspidalTCStatement.{uF,uE,uV,uW}

/-- Use the equal-rank twist inputs of the completed pair equations. -/
theorem cyclicWeakInductionSupercuspidalFromPairEquations :
    CyclicWeakInductionSupercuspidalFromPairEquationsStatement.{uF,uE,uV,uW} := by
  intro hF hE
  exact supercuspidality_of_twistEquations
    (equalRankTwistEngineInputs_of_globalEquation hF) (equalRankTwistEngineInputs_of_globalEquation hE)

/-- The equal-rank semi-local equation in the two field and presentation universes
suffices for both cyclic weak-induction supercuspidality statements. -/
def CyclicWeakInductionSupercuspidalFromEqualSemilocalStatement : Prop :=
  EqualSemilocalEquationStatement.{uF,uV} →
  EqualSemilocalEquationStatement.{uE,uW} →
  CyclicWeakInductionSupercuspidalStatement.{uF,uE,uV,uW} ∧
    CyclicWeakInductionSupercuspidalTCStatement.{uF,uE,uV,uW}

/-- Use only the equal-rank semi-local equations for the self-pair comparisons. -/
theorem cyclicWeakInductionSupercuspidalFromEqualSemilocal :
    CyclicWeakInductionSupercuspidalFromEqualSemilocalStatement.{uF,uE,uV,uW} := by
  intro hF hE
  exact supercuspidality_of_twistEquations
    (equalRankTwistEngineInputs_of_semilocalEquation hF)
    (equalRankTwistEngineInputs_of_semilocalEquation hE)

end Langlands.Automorphic.Unramified
