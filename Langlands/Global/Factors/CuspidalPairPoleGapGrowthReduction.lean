import Langlands.Global.Factors.CuspidalPairPoleRemainingInputs
import Langlands.Global.RankinSelberg.RealLocalPositiveEqualReduction
import Langlands.Global.RankinSelberg.RealUniformCanonicalRange

/-! # Real ordinary strip growth from model uniformity and unequal growth at rank gaps of at least two -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u uQ

namespace Langlands.Global.RankinSelbergGlobal

open LocalFactor.Archimedean ArchimedeanLocal

/-- Ordinary unequal-rank real tests: every entire normalization has exponential strip growth,
given model uniformity and unequal character-list growth at the two ranks. The tests of block
lists are carried to character lists by the uniform character-list inclusion. -/
theorem realOrdinaryUnequalTest_stripGrowth_of_characterList
    (hU : RealWhittakerModelUniformityStatement)
    {r t : ℕ} (h : t < r) (hG : RealJacquet.RealLocalUnequalCharacterGrowthAtRanks r t h)
    (d e : List RealBlock) (hd : realRank d = r + 1) (he : realRank e = t + 1) (a : ℝˣ)
    (D : RealQuotientMeasureData t) :
    HasOrdinaryNormalizationStripGrowth (realOrdinaryUnequalTest h d e a D)
      (realPairLFactor d e) := by
  refine hasOrdinaryNormalizationStripGrowth_real_of_raw _ d e fun i => ?_
  obtain ⟨L, hL, -, hLr, hLle⟩ := RealJacquet.realUniformCharacterListInclusion r d hd a
  obtain ⟨L', hL', -, hL'r, hL'le⟩ := RealJacquet.realUniformCharacterListInclusion t e he (-a)
  exact (hG L L' hL hL' hLr hL'r a D i.1 i.2 (hLle (hU r d hd a i.1.2))
    (hL'le (hU t e he (-a) i.2.2))).exists_meromorphic_stripGrowth

/-- Ordinary equal-rank real tests: every entire normalization has exponential strip growth,
given model uniformity and equal character-list growth at the rank. -/
theorem realOrdinaryEqualTest_stripGrowth_of_characterList
    (hU : RealWhittakerModelUniformityStatement)
    {r : ℕ} (hG : RealJacquet.RealLocalEqualCharacterGrowthAtRank r)
    (d e : List RealBlock) (hd : realRank d = r + 1) (he : realRank e = r + 1) (a : ℝˣ)
    (D : RealQuotientMeasureData r) :
    HasOrdinaryNormalizationStripGrowth (realOrdinaryEqualTest r d e a D)
      (realPairLFactor d e) := by
  refine hasOrdinaryNormalizationStripGrowth_real_of_raw _ d e fun i => ?_
  obtain ⟨L, hL, -, hLr, hLle⟩ := RealJacquet.realUniformCharacterListInclusion r d hd a
  obtain ⟨L', hL', -, hL'r, hL'le⟩ := RealJacquet.realUniformCharacterListInclusion r e he (-a)
  exact (hG L L' hL hL' hLr hL'r a D i.1 i.2.1 i.2.2 (hLle (hU r d hd a i.1.2))
    (hL'le (hU r e he (-a) i.2.1.2))).exists_meromorphic_stripGrowth

/-- Real ordinary normalized strip growth from real Whittaker model uniformity and unequal
character-list growth at every pair of ranks whose indices differ by at least two. -/
def RealOrdinaryStripGrowthGapStatement : Prop :=
  RealWhittakerModelUniformityStatement →
    (∀ (r t : ℕ) (h : t < r), t + 1 < r → RealJacquet.RealLocalUnequalCharacterGrowthAtRanks r t h) →
    CuspidalPairPoles.RealOrdinaryNormalizedStripGrowthStatement

theorem realOrdinaryStripGrowthGap : RealOrdinaryStripGrowthGapStatement := by
  intro hU hGap
  have hEqual : ∀ r : ℕ, RealJacquet.RealLocalEqualCharacterGrowthAtRank r :=
    RealJacquet.realLocalEqualCharacterGrowth_of_canonicalPremises
      RealUniformCanonicalRange.realUniformCanonicalRangePremise
      RealUniformCanonicalRange.realCanonicalStandardEvaluationPremise
  have hUnequal (r t : ℕ) (h : t < r) : RealJacquet.RealLocalUnequalCharacterGrowthAtRanks r t h := by
    by_cases hg : t + 1 < r
    · exact hGap r t h hg
    · obtain rfl : r = t + 1 := by omega
      exact RealJacquet.realAdjacentFromEqualGrowth
        RealUniformCanonicalRange.realUniformCanonicalRangePremise
        (RealJacquet.realOrthogonalCompactProjectionPremise t) (hEqual t)
  exact ⟨fun r t h d e hd he a =>
      realOrdinaryUnequalTest_stripGrowth_of_characterList hU h (hUnequal r t h) d e hd he a _,
    fun r d e hd he a =>
      realOrdinaryEqualTest_stripGrowth_of_characterList hU (hEqual r) d e hd he a _⟩

end Langlands.Global.RankinSelbergGlobal

namespace Langlands.Global.CuspidalPairPoles

open RankinSelbergGlobal

/-- The completed functional equation, the real ordinary continuation, the real and complex
ordinary generation, the three archimedean Whittaker range statements, real Whittaker model
uniformity and unequal real character-list growth at rank gaps of at least two imply the
cuspidal pair pole proposition in both universes. -/
def CuspidalPairPoleGapGrowthInputsStatement : Prop :=
  CuspidalPairGlobalFunctionalEquationStatement.{u,uQ} →
  RealOrdinaryNormalizedContinuationStatement → RealOrdinaryNormalizedGenerationStatement →
  ComplexOrdinaryNormalizedGenerationStatement →
  InfiniteWhittakerSliceModelStatement.{u,uQ} →
  RealPlaceWhittakerRestrictionSurjectivityStatement.{u} →
  ComplexPlaceWhittakerRestrictionSurjectivityStatement.{u} →
  RealWhittakerModelUniformityStatement →
  (∀ (r t : ℕ) (h : t < r), t + 1 < r → RealJacquet.RealLocalUnequalCharacterGrowthAtRanks r t h) →
  CuspidalPairPoleStatement.{u,uQ}

theorem cuspidalPairPoleGapGrowthInputs : CuspidalPairPoleGapGrowthInputsStatement.{u,uQ} := by
  intro hFE hRC hRG hCG hSlice hReal hComplex hU hGap
  exact cuspidalPairPoleRemainingInputs hFE hRC hRG hCG (realOrdinaryStripGrowthGap hU hGap)
    hSlice hReal hComplex

end Langlands.Global.CuspidalPairPoles
