import Langlands.Global.RankinSelberg.RealAdjacentCanonical
import Langlands.Global.RankinSelberg.RealOrthogonalCompactProjection
import Langlands.Global.RankinSelberg.RealUniformTailInclusion

/-! # The real positive equal-rank continuation from the canonical premises

See the paired Markdown file.
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.RealJacquet

/-- Equal-rank character growth holds at every rank, given the canonical range and canonical
evaluation premises. -/
theorem realLocalEqualCharacterGrowth_of_canonicalPremises
    (hRange : RealGodement.RealUniformCanonicalRangePremise)
    (hEval : RealGodement.RealCanonicalStandardEvaluationPremise) :
    ∀ r : ℕ, RealLocalEqualCharacterGrowthAtRank r := by
  intro r
  induction r with
  | zero => exact realLocalEqualCharacterGrowthAtRank_zero
  | succ t ih =>
    exact RealGodement.realLocalEqualGrowthStep t hRange hEval
      (RealGodement.realMatrixCoefficientGrowth t)
      (realAdjacentFromEqualGrowth hRange (realOrthogonalCompactProjectionPremise t) ih)

/-- The positive equal-rank continuation target follows from the canonical range premise and the
canonical evaluation premise. -/
def RealLocalUniformPositiveEqualContinuationCanonicalPremisesStatement : Prop :=
  RealGodement.RealUniformCanonicalRangePremise →
    RealGodement.RealCanonicalStandardEvaluationPremise →
    RealLocalUniformPositiveEqualContinuationStatement

theorem realLocalUniformPositiveEqualContinuation_of_canonicalPremises :
    RealLocalUniformPositiveEqualContinuationCanonicalPremisesStatement :=
  fun hRange hEval =>
    realLocalUniformPositiveEqualContinuation_of_equalCharacterGrowth fun r _ =>
      realLocalEqualCharacterGrowth_of_canonicalPremises hRange hEval r

end Langlands.Global.RankinSelbergGlobal.RealJacquet
