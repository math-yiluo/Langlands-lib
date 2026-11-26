import Langlands.Global.Factors.CuspidalPairPoleRemainingInputs
import Langlands.Global.RankinSelberg.ArchimedeanRealPairIdentityStripGrowth
import Langlands.Global.RankinSelberg.RankOneOrdinaryStripGrowth
import Langlands.Global.RankinSelberg.OrdinaryNormalizationUniqueness

/-! # Real ordinary continuation and strip growth from the uniform pair identities -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u uQ

namespace Langlands.Global.RankinSelbergGlobal

open LocalFactor.Archimedean ArchimedeanLocal
open FunctionalEquationComparison.CompletedEquationAdapter (realPairLFactor_denominator_ne_zero)
open ArchimedeanRealPairIdentity

/-- Real Whittaker model uniformity and the two uniform real pair-identity premises give every
real ordinary test an entire normalization, and give every such normalization exponential strip
growth. -/
def RealOrdinaryNormalizedAllGrowthPairIdentityStatement : Prop :=
  RealWhittakerModelUniformityStatement → RealLocalUniformUnequalPairIdentityStatement →
    RealLocalUniformPositiveEqualPairIdentityStatement →
    RealOrdinaryNormalizedContinuationStatement ∧
      CuspidalPairPoles.RealOrdinaryNormalizedStripGrowthStatement

theorem realOrdinaryNormalizedAllGrowthPairIdentity :
    RealOrdinaryNormalizedAllGrowthPairIdentityStatement := by
  intro hU hPU hPE
  have hUnequal (r t : ℕ) (h : t < r) (d e : List RealBlock) (hd : realRank d = r + 1)
      (he : realRank e = t + 1) (a : ℝˣ) (D : RealQuotientMeasureData t) :
      HasEntireOrdinaryNormalizations (realOrdinaryUnequalTest h d e a D) (realPairLFactor d e) ∧
      HasOrdinaryNormalizationStripGrowth (realOrdinaryUnequalTest h d e a D)
        (realPairLFactor d e) := by
    refine ordinaryNormalizationGrowthFromExistence _ _ (realPairLFactor_denominator_ne_zero d e) ?_
    rintro ⟨W, V⟩
    exact realUniformUnequalNormalization_of_pairIdentity hPU h hd he a D
      (hU r d hd a W.2) (hU t e he (-a) V.2)
  have hEqual (r : ℕ) (d e : List RealBlock) (hd : realRank d = r + 1)
      (he : realRank e = r + 1) (a : ℝˣ) (D : RealQuotientMeasureData r) :
      HasEntireOrdinaryNormalizations (realOrdinaryEqualTest r d e a D) (realPairLFactor d e) ∧
      HasOrdinaryNormalizationStripGrowth (realOrdinaryEqualTest r d e a D)
        (realPairLFactor d e) := by
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · exact rankOneOrdinaryStripGrowth.1 d e hd he a D
    · refine ordinaryNormalizationGrowthFromExistence _ _
        (realPairLFactor_denominator_ne_zero d e) ?_
      rintro ⟨W, V, Φ⟩
      exact realUniformPositiveEqualNormalization_of_pairIdentity hPE hr hd he a D Φ
        (hU r d hd a W.2) (hU r e he (-a) V.2)
  exact ⟨⟨fun r t h d e hd he a D => (hUnequal r t h d e hd he a D).1,
      fun r d e hd he a D => (hEqual r d e hd he a D).1⟩,
    ⟨fun r t h d e hd he a => (hUnequal r t h d e hd he a (realQuotientMeasureData t)).2,
      fun r d e hd he a => (hEqual r d e hd he a (realQuotientMeasureData r)).2⟩⟩

end Langlands.Global.RankinSelbergGlobal

namespace Langlands.Global.CuspidalPairPoles

open RankinSelbergGlobal

/-- The completed functional equation, the real and complex ordinary generation, the three
archimedean Whittaker range statements, real Whittaker model uniformity and the two uniform
real pair-identity premises imply the cuspidal pair pole proposition in both universes. -/
def CuspidalPairPolePairIdentityPremisesStatement : Prop :=
  CuspidalPairGlobalFunctionalEquationStatement.{u,uQ} →
  RealOrdinaryNormalizedGenerationStatement → ComplexOrdinaryNormalizedGenerationStatement →
  InfiniteWhittakerSliceModelStatement.{u,uQ} →
  RealPlaceWhittakerRestrictionSurjectivityStatement.{u} →
  ComplexPlaceWhittakerRestrictionSurjectivityStatement.{u} →
  RealWhittakerModelUniformityStatement → RealLocalUniformUnequalPairIdentityStatement →
  RealLocalUniformPositiveEqualPairIdentityStatement →
  CuspidalPairPoleStatement.{u,uQ}

theorem cuspidalPairPolePairIdentityPremises :
    CuspidalPairPolePairIdentityPremisesStatement.{u,uQ} := by
  intro hFE hRG hCG hSlice hReal hComplex hU hPU hPE
  have hR := realOrdinaryNormalizedAllGrowthPairIdentity hU hPU hPE
  exact cuspidalPairPoleRemainingInputs hFE hR.1 hRG hCG hR.2 hSlice hReal hComplex

end Langlands.Global.CuspidalPairPoles
