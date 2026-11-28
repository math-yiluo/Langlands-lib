import Langlands.Global.RankinSelberg.RealCanonicalOrdinaryDeformation
import Langlands.Global.RankinSelberg.RealLocalUniformUnequalContinuationProof
import Langlands.Global.RankinSelberg.RealTemperedWhittakerBoundProof
import Langlands.Global.RankinSelberg.RealUniformCanonicalRange

/-! # Ordinary normalized continuation over the real field -/

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

open RealBlockParameters RealJacquet RealPrincipalSeries

/-- Every ordinary real Rankin–Selberg test has an entire normalization by the prescribed
block pair factor in both rank regimes. -/
theorem realOrdinaryNormalizedContinuation : RealOrdinaryNormalizedContinuationStatement := by
  have hRange := RealUniformCanonicalRange.realUniformCanonicalRangePremise
  have hEval := RealUniformCanonicalRange.realCanonicalStandardEvaluationPremise
  refine realOrdinaryBlockAssembly realLocalUnequalCharacterGrowth
    (fun r _ => realLocalEqualCharacterGrowth_of_canonicalPremises hRange hEval r)
    RealTemperedWhittaker.realTemperedWhittakerBound ?_
  refine realOrdinaryHolomorphicTestFamilies_of_ascending hRange ?_
  intro r ds hr a
  rw [← realWhittakerModels_eq r (ascendingExpand ds) ((realRank_ascendingExpand ds).trans hr) a,
    realAscendingWhittakerModels_eq r ds hr a]

end Langlands.Global.RankinSelbergGlobal
