import Langlands.Representation.RankinSelberg.AdjacentRankAdmissibility
import Langlands.AllField.Representation.Parabolic.LeviInflationAdmissibilityProof
import Langlands.AllField.Representation.RankinSelberg.AdjacentRankSectionSurjectivity
/-! Admissibility of the actual adjacent induction and closed fixed coefficients. -/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement RankOneWhittakerTypeStatement TwoBlockWhittakerDeformationStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement adjacentRankDeterminantWeight adjacentRankDeterminantWeight_apply adjacentRankDeterminantWeight_locallyConstant adjacentRankLowerScalarProjection adjacentRankLower_determinantComplexPower adjacentRankLower_halfModulus adjacentRankLower_weightRatio isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt lastRowCompactOrbit normalizedAbsoluteValue normalizedAbsoluteValue_apply rankOneCharacter_isOfWhittakerType rankOneExtensionCharacter rankOneExtensionCharacter_isOfWhittakerType rankOneExtensionCharacter_isSmooth rankOneWhittakerType twoBlockDeformedBlocks twoBlockDeformedBlocks_zero twoBlockDeformedInduced
open Langlands.AllField.RankinSelberg

open Langlands.HarmonicAnalysis hiding padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis

universe uF uV uG

section Projection


end Projection

namespace Padic
open Langlands.RankinSelberg.Padic hiding adjacentAdmissibilityLocalField adjacentAdmissibilityTopology adjacentAdmissibilityValuativeRel adjacentRankLowerCompactRepresentation adjacentRankLowerInducingCoordinates adjacentRankLowerTensorCoordinates_action adjacentRankLowerTensorRepresentation adjacentRankLowerTensorRepresentation_isAdmissible adjacentRankNormalizedInduced_isAdmissible adjacentRankNormalizedSection adjacentRankNormalizedSectionTensor adjacentRankNormalizedSectionTensor_surjective adjacentRankNormalizedSectionTensor_tmul adjacentRankNormalizedSection_eval adjacentRankNormalizedSection_right adjacentSectionFieldTopology adjacentSectionGLBorel adjacentSectionGLMeasurable adjacentSectionLocalField adjacentSectionT2 adjacentSectionValuativeRel oppositeParabolicQuotientCompact sectionSurjectivityGLBorel sectionSurjectivityGLMeasurable sectionSurjectivityLocalField sectionSurjectivityT2 sectionSurjectivityTopology sectionSurjectivityValuativeRel
open Langlands.AllField.RankinSelberg.Padic
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement RankOneWhittakerTypeStatement TwoBlockWhittakerDeformationStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement adjacentRankDeterminantWeight adjacentRankDeterminantWeight_apply adjacentRankDeterminantWeight_locallyConstant adjacentRankLowerScalarProjection adjacentRankLower_determinantComplexPower adjacentRankLower_halfModulus adjacentRankLower_weightRatio isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt lastRowCompactOrbit normalizedAbsoluteValue normalizedAbsoluteValue_apply rankOneCharacter_isOfWhittakerType rankOneExtensionCharacter rankOneExtensionCharacter_isOfWhittakerType rankOneExtensionCharacter_isSmooth rankOneWhittakerType twoBlockDeformedBlocks twoBlockDeformedBlocks_zero twoBlockDeformedInduced
open Langlands.AllField.RankinSelberg

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

variable {r : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (σ : Representation ℂ (GeneralLinear (r + 1) F) V)
  (χ : Quasicharacter F)

/-- Admissibility of the original representation implies admissibility of the
actual normalized lower-parabolic inducing action on its exact tensor carrier. -/
theorem adjacentRankLowerTensorRepresentation_isAdmissible (hσ : IsAdmissible σ) :
    IsAdmissible (adjacentRankLowerTensorRepresentation F σ χ) := by
  let P := (adjacentRankLowerShape r).oppositeParabolic F
  let a := adjacentRankLowerLargeProjection (K := F) (r := r)
  let ξ := adjacentRankDeterminantWeight (⟨⟩ : LocalFieldData F) χ
    (r + 1) ((r + 2 : ℕ) / 2)
  let θ := adjacentRankDeterminantWeight (⟨⟩ : LocalFieldData F) χ
    (r + 2) ((r + 1 : ℕ) / 2)
  have ha : Continuous a := continuous_adjacentRankLowerLargeProjection
  have hcomp : IsAdmissible (σ.comp a) :=
    (isAdmissible_comp_iff_of_open_surjective σ a ha
      isOpenMap_adjacentRankLowerLargeProjection
      adjacentRankLowerLargeProjection_surjective).mpr hσ
  let φ₁ : P →* ℂˣ := θ.toMonoidHom.comp P.subtype
  let φ₂ : P →* ℂˣ := ξ.toMonoidHom.comp a
  have h₁ : IsOpen (φ₁.ker : Set P) := by
    rw [← MonoidHom.comap_ker, Subgroup.coe_comap]
    exact θ.isOpen_ker.preimage continuous_subtype_val
  have h₂ : IsOpen (φ₂.ker : Set P) := by
    rw [← MonoidHom.comap_ker, Subgroup.coe_comap]
    exact ξ.isOpen_ker.preimage ha
  have hker : IsOpen ((φ₁ * φ₂⁻¹).ker : Set P) := by
    refine Subgroup.isOpen_mono (H₁ := φ₁.ker ⊓ φ₂.ker) ?_ ?_
    · intro q hq
      change φ₁ q * (φ₂ q)⁻¹ = 1
      rw [show φ₁ q = 1 from hq.1, show φ₂ q = 1 from hq.2]
      simp
    · exact h₁.inter h₂
  have hc : IsAdmissible (adjacentRankLowerCompactRepresentation F σ χ) :=
    (isAdmissible_twist_iff (φ₁ * φ₂⁻¹) (σ.comp a) hker).mpr hcomp
  exact isAdmissible_of_equiv (adjacentRankLowerInducingCoordinates F σ χ).symm hc

/-- The exact canonical normalized opposite induction on the original tensor
carrier is admissible for every continuous quasicharacter. -/
theorem adjacentRankNormalizedInduced_isAdmissible (hσ : IsAdmissible σ) :
    IsAdmissible
      ((⟨⟩ : LocalFieldData F).normalizedOppositeParabolicInduced (adjacentRankLowerShape r)
        ((adjacentRankLowerShape r).blockTensor
          (Shahidi.pairFamily σ (rankOneExtensionCharacter.{uF, uV} F χ)))) := by
  let := oppositeParabolicQuotientCompact F (⟨⟩ : LocalFieldData F)
    (adjacentRankLowerShape r)
  exact Induction.smoothInduced_isAdmissible_of_compactSpace _
    (adjacentRankLowerTensorRepresentation F σ χ)
    (adjacentRankLowerTensorRepresentation_isAdmissible F σ χ hσ)

end Padic

section Coefficients


end Coefficients

end Langlands.AllField.RankinSelberg
