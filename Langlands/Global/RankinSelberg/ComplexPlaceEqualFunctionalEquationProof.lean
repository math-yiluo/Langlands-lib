import Langlands.Global.RankinSelberg.ComplexAdjacentFromEqualGrowth
import Langlands.Global.RankinSelberg.ComplexLocalEqualGrowthReduction
import Langlands.Global.RankinSelberg.ComplexLocalEqualGrowthStep
import Langlands.Global.RankinSelberg.ComplexLocalEqualRankZeroGrowth

/-! # The local complex equal-rank Rankin–Selberg functional equation -/

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

open ComplexJacquet ComplexJacquetContinuation

private theorem identityProportionality : ComplexJacquetIdentityProportionality := by
  intro r μ a l p B hB
  obtain ⟨c, hc⟩ := (ComplexJacquetMultiplicityOne.complexJacquetMultiplicityOne r μ a l p).1 B hB
  exact ⟨c, fun f => congrArg (fun T => T f 1) hc⟩

/-- The equal-rank local complex equation for the published compact-finite Whittaker models. -/
theorem complexLocalEqualFunctionalEquation : ComplexLocalEqualFunctionalEquationStatement := by
  apply complexLocalEqualGrowthReduction
  show ∀ r, ComplexLocalEqualGrowthAtRank r
  intro r
  induction r with
  | zero => exact complexLocalEqualRankZeroGrowth
  | succ r ih =>
      exact complexLocalEqualGrowthStep identityProportionality (complexAdjacentFromEqualGrowth r ih)

end Langlands.Global.RankinSelbergGlobal
