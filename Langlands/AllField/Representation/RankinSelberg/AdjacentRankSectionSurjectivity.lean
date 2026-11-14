import Langlands.Representation.RankinSelberg.AdjacentRankSectionSurjectivity
import Langlands.AllField.Representation.Induction.Equivalences
import Langlands.AllField.Representation.Induction.InverseTranspose
import Langlands.AllField.Representation.RankinSelberg.AdjacentRankNormalizedSection
/-! Surjectivity of the actual normalized rectangular-section tensor map. -/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement RankOneWhittakerTypeStatement TwoBlockWhittakerDeformationStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement adjacentRankDeterminantWeight adjacentRankDeterminantWeight_apply adjacentRankDeterminantWeight_locallyConstant adjacentRankLowerScalarProjection adjacentRankLower_determinantComplexPower adjacentRankLower_halfModulus adjacentRankLower_weightRatio isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt lastRowCompactOrbit normalizedAbsoluteValue normalizedAbsoluteValue_apply rankOneCharacter_isOfWhittakerType rankOneExtensionCharacter rankOneExtensionCharacter_isOfWhittakerType rankOneExtensionCharacter_isSmooth rankOneWhittakerType twoBlockDeformedBlocks twoBlockDeformedBlocks_zero twoBlockDeformedInduced
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory Matrix
open Langlands.HarmonicAnalysis hiding padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.Induction hiding SmoothRep
open scoped TensorProduct

universe uF uV

section General

variable {K : Type uF} [Field K] [TopologicalSpace K]
  [IsTopologicalDivisionRing K] [T2Space K] {r : ℕ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

private abbrev P := (adjacentRankLowerShape r).oppositeParabolic K
private abbrev a : P (K := K) (r := r) →* GeneralLinear (r + 1) K :=
  adjacentRankLowerLargeProjection


end General

namespace Padic
open Langlands.RankinSelberg.Padic hiding adjacentRankLowerCompactRepresentation adjacentRankLowerInducingCoordinates adjacentRankLowerTensorCoordinates_action adjacentRankLowerTensorRepresentation adjacentRankNormalizedSection adjacentRankNormalizedSectionTensor adjacentRankNormalizedSectionTensor_surjective adjacentRankNormalizedSectionTensor_tmul adjacentRankNormalizedSection_eval adjacentRankNormalizedSection_right adjacentSectionFieldTopology adjacentSectionGLBorel adjacentSectionGLMeasurable adjacentSectionLocalField adjacentSectionT2 adjacentSectionValuativeRel oppositeParabolicQuotientCompact sectionSurjectivityGLBorel sectionSurjectivityGLMeasurable sectionSurjectivityLocalField sectionSurjectivityT2 sectionSurjectivityTopology sectionSurjectivityValuativeRel
open Langlands.AllField.RankinSelberg.Padic
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement RankOneWhittakerTypeStatement TwoBlockWhittakerDeformationStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement adjacentRankDeterminantWeight adjacentRankDeterminantWeight_apply adjacentRankDeterminantWeight_locallyConstant adjacentRankLowerScalarProjection adjacentRankLower_determinantComplexPower adjacentRankLower_halfModulus adjacentRankLower_weightRatio isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt lastRowCompactOrbit normalizedAbsoluteValue normalizedAbsoluteValue_apply rankOneCharacter_isOfWhittakerType rankOneExtensionCharacter rankOneExtensionCharacter_isOfWhittakerType rankOneExtensionCharacter_isSmooth rankOneWhittakerType twoBlockDeformedBlocks twoBlockDeformedBlocks_zero twoBlockDeformedInduced
open Langlands.AllField.RankinSelberg

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

/-- Inverse transpose takes a compact integral-group cover for the upper quotient
to a compact cover for the actual opposite quotient, in every block shape. -/
theorem oppositeParabolicQuotientCompact (T : LocalFieldData F)
    {n : ℕ} (B : GeneralLinear.BlockShape n) :
    letI := T.topology
    CompactSpace (LeftQuotient (B.oppositeParabolic F)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have hcover :
      (fun g => quotientMap (B.oppositeParabolic F)
        (GeneralLinear.inverseTranspose n F g)) ''
        (GeneralLinear.Iwasawa.integralRange (ValuativeRel.valuation F) n :
          Set (GeneralLinear n F)) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    induction x using Quotient.inductionOn with
    | h g =>
      have hg := Set.mem_univ
        (quotientMap (B.parabolic F)
          (GeneralLinear.inverseTranspose n F g))
      rw [← Langlands.AllField.Parabolic.quotientMap_image_integralRange T B] at hg
      obtain ⟨k, hk, hkg⟩ := hg
      refine ⟨k, hk, Quotient.sound ?_⟩
      apply QuotientGroup.rightRel_apply.mpr
      have hr : GeneralLinear.inverseTranspose n F g * k⁻¹ ∈
          B.parabolic F :=
        QuotientGroup.rightRel_apply.mp (Quotient.exact hkg)
      have ho := (B.inverseTranspose_mem_oppositeParabolic_iff F _).mpr hr
      simpa only [map_mul, map_inv, GeneralLinear.inverseTranspose_involutive] using ho
  constructor
  rw [← hcover]
  exact (Langlands.AllField.Parabolic.isCompact_integralRange T n).image
    (continuous_quotient_mk'.comp (GeneralLinear.continuous_inverseTranspose n F))

local instance sectionSurjectivityT2 : T2Space F :=
  (⟨⟩ : LocalFieldData F).fieldT2
local instance sectionSurjectivityGLMeasurable (n : ℕ) :
    MeasurableSpace (GeneralLinear (n + 1) F) := borel _
local instance sectionSurjectivityGLBorel (n : ℕ) :
    BorelSpace (GeneralLinear (n + 1) F) := ⟨rfl⟩

variable {r : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (σ : Representation ℂ (GeneralLinear (r + 1) F) V)
  (χ : Quasicharacter F)

/-- Every vector of the exact canonical normalized opposite-parabolic induction
comes from the original compact-test/vector algebraic tensor product. -/
theorem adjacentRankNormalizedSectionTensor_surjective (hσ : IsSmooth σ) :
    Function.Surjective (adjacentRankNormalizedSectionTensor F σ χ hσ) := by
  let := oppositeParabolicQuotientCompact F (⟨⟩ : LocalFieldData F)
    (adjacentRankLowerShape r)
  have hbasis : ∀ O : Set (GeneralLinear (r + 2) F), IsOpen O → 1 ∈ O →
      ∃ J : OpenSubgroup (GeneralLinear (r + 2) F),
        IsCompact (J : Set (GeneralLinear (r + 2) F)) ∧
        (J : Set (GeneralLinear (r + 2) F)) ⊆ O := by
    intro O hO h1
    let J := (⟨⟩ : LocalFieldData F).generalLinearCompactOpen (r + 2) O
      (hO.mem_nhds h1)
    exact ⟨J.val, J.property⟩
  have hs := adjacentRankLowerSectionTensor_surjective
    (generalLinearHaar F r) σ hσ
    (adjacentRankDeterminantWeight (⟨⟩ : LocalFieldData F) χ
      (r + 1) ((r + 2 : ℕ) / 2)).toMonoidHom
    (adjacentRankDeterminantWeight_locallyConstant (⟨⟩ : LocalFieldData F) χ
      (r + 1) ((r + 2 : ℕ) / 2))
    (fun q => measurePreserving_mul_right (generalLinearHaar F r)
      (adjacentRankLowerLargeProjection q)) hbasis
    (adjacentRankDeterminantWeight (⟨⟩ : LocalFieldData F) χ
      (r + 2) ((r + 1 : ℕ) / 2))
  exact (smoothInducedEquiv _
    (adjacentRankLowerInducingCoordinates F σ χ).symm).toLinearEquiv.surjective.comp hs

end Padic

end Langlands.AllField.RankinSelberg
