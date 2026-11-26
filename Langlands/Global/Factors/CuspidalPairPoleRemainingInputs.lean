import Langlands.Global.RankinSelberg.ComplexOrdinaryNormalizedAllGrowth
import Langlands.Global.RankinSelberg.RealOrdinaryStripGrowthReduction

/-! # The cuspidal pair pole theorem from its functional-equation, local and real growth inputs -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u uQ

namespace Langlands.Global.CuspidalPairPoles

open RankinSelbergGlobal

/-- The completed functional equation, the real ordinary continuation, the real and complex
ordinary generation, the real ordinary strip growth and the three archimedean Whittaker range
statements imply the cuspidal pair pole proposition in both universes. -/
def CuspidalPairPoleRemainingInputsStatement : Prop :=
  CuspidalPairGlobalFunctionalEquationStatement.{u,uQ} →
  RealOrdinaryNormalizedContinuationStatement → RealOrdinaryNormalizedGenerationStatement →
  ComplexOrdinaryNormalizedGenerationStatement → RealOrdinaryNormalizedStripGrowthStatement →
  InfiniteWhittakerSliceModelStatement.{u,uQ} →
  RealPlaceWhittakerRestrictionSurjectivityStatement.{u} →
  ComplexPlaceWhittakerRestrictionSurjectivityStatement.{u} →
  CuspidalPairPoleStatement.{u,uQ}

theorem cuspidalPairPoleRemainingInputs : CuspidalPairPoleRemainingInputsStatement.{u,uQ} := by
  intro hFE hRC hRG hCG hRS hSlice hReal hComplex
  exact cuspidalPairPoleFromLocalTests hFE
    ⟨⟨hRC, complexOrdinaryNormalizedAllGrowth.1, hRG, hCG⟩, hRS,
      complexOrdinaryNormalizedAllGrowth.2,
      fun _ _ _ _ => specifiedWhittakerSliceComparisonAt_of_local hSlice hReal hComplex⟩

/-- The same implication with the real ordinary strip growth replaced by the premises of
`RealOrdinaryStripGrowthPremisesStatement`: real Whittaker model uniformity, the uniform
principal-series inclusion, the canonical range, canonical evaluation and matrix-coefficient
premises of the real equal-rank successor step, and unequal real character-list growth at all
pairs of ranks. -/
def CuspidalPairPoleRealPremisesStatement : Prop :=
  CuspidalPairGlobalFunctionalEquationStatement.{u,uQ} →
  RealOrdinaryNormalizedContinuationStatement → RealOrdinaryNormalizedGenerationStatement →
  ComplexOrdinaryNormalizedGenerationStatement →
  InfiniteWhittakerSliceModelStatement.{u,uQ} →
  RealPlaceWhittakerRestrictionSurjectivityStatement.{u} →
  ComplexPlaceWhittakerRestrictionSurjectivityStatement.{u} →
  RealWhittakerModelUniformityStatement → RealUniformPrincipalSeriesInclusionStatement →
  RealGodement.RealUniformCanonicalRangePremise →
  RealGodement.RealCanonicalStandardEvaluationPremise →
  (∀ t : ℕ, RealGodement.RealMatrixCoefficientGrowthPremise t) →
  (∀ (r t : ℕ) (h : t < r), RealJacquet.RealLocalUnequalCharacterGrowthAtRanks r t h) →
  CuspidalPairPoleStatement.{u,uQ}

theorem cuspidalPairPoleRealPremises : CuspidalPairPoleRealPremisesStatement.{u,uQ} := by
  intro hFE hRC hRG hCG hSlice hReal hComplex hU hI hRange hEval hMat hUnequal
  exact cuspidalPairPoleRemainingInputs hFE hRC hRG hCG
    (realOrdinaryStripGrowthPremises hU hI hRange hEval hMat hUnequal) hSlice hReal hComplex

end Langlands.Global.CuspidalPairPoles
