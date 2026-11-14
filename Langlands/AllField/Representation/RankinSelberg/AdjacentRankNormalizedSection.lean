import Langlands.Representation.RankinSelberg.AdjacentRankNormalizedSection
import Langlands.AllField.Representation.RankinSelberg.LastRowCompactOrbitProof
import Langlands.AllField.Representation.RankinSelberg.RankOneExtensionCharacter
import Langlands.AllField.Representation.RankinSelberg.TwoBlockJacquetConvergence.RadicalIwasawa
/-! Compact-orbit sections in the exact normalized adjacent-rank lower induction. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

open scoped BigOperators TensorProduct NNReal

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement RankOneWhittakerTypeStatement TwoBlockWhittakerDeformationStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement adjacentRankDeterminantWeight adjacentRankDeterminantWeight_apply adjacentRankDeterminantWeight_locallyConstant adjacentRankLowerScalarProjection adjacentRankLower_determinantComplexPower adjacentRankLower_halfModulus adjacentRankLower_weightRatio isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt lastRowCompactOrbit normalizedAbsoluteValue normalizedAbsoluteValue_apply rankOneCharacter_isOfWhittakerType rankOneExtensionCharacter rankOneExtensionCharacter_isOfWhittakerType rankOneExtensionCharacter_isSmooth rankOneWhittakerType twoBlockDeformedBlocks twoBlockDeformedBlocks_zero twoBlockDeformedInduced
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory Matrix
open Langlands.HarmonicAnalysis hiding padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis

universe uF uV

section PadicCharacters

variable {F : Type uF} [Field F]
  (T : LocalFieldData F)

/-- The smooth determinant weight `χ(det g) |det g|^s`. -/
def adjacentRankDeterminantWeight
    (χ : letI := T.topology; Quasicharacter F) (n : ℕ) (s : ℂ) :
    letI := T.topology
    Induction.SmoothCharacter ℂ (GeneralLinear n F) := by
  letI := T.topology
  letI := T.generalLinearNonarchimedean n
  refine ⟨(χ : Fˣ →* ℂˣ).comp GeneralLinear.determinant *
    T.determinantComplexPower n s, ?_⟩
  apply isOpen_ker_of_continuous_complex_character
  change Continuous (fun g : GeneralLinear n F =>
    χ (GeneralLinear.determinant g) *
      T.unramifiedCharacter
        (LocalFactor.spectralParameter T.residueCardinality T.residueCardinality_real_pos s)
        (GeneralLinear.determinant g))
  exact (χ.continuous.mul (T.continuous_unramifiedCharacter _)).comp
    (T.generalLinearDeterminant n).continuous

@[simp] theorem adjacentRankDeterminantWeight_apply
    (χ : letI := T.topology; Quasicharacter F) (n : ℕ) (s : ℂ)
    (g : GeneralLinear n F) :
    letI := T.topology
    (adjacentRankDeterminantWeight T χ n s).toMonoidHom g =
      χ (GeneralLinear.determinant g) * T.determinantComplexPower n s g := rfl

/-- The scalar inner weight is locally constant on the actual general linear group. -/
theorem adjacentRankDeterminantWeight_locallyConstant
    (χ : letI := T.topology; Quasicharacter F) (n : ℕ) (s : ℂ) :
    letI := T.topology
    IsLocallyConstant (fun g : GeneralLinear n F =>
      ((adjacentRankDeterminantWeight T χ n s).toMonoidHom g : ℂ)) := by
  let := T.topology
  let := T.generalLinearNonarchimedean n
  apply isLocallyConstant_of_continuous_complex_character
  exact (χ.continuous.mul (T.continuous_unramifiedCharacter _)).comp
    (T.generalLinearDeterminant n).continuous

/-- The actual determinant power splits over the two lower diagonal blocks. -/
theorem adjacentRankLower_determinantComplexPower {r : ℕ}
    (q : (adjacentRankLowerShape r).oppositeParabolic F) (s : ℂ) :
    T.determinantComplexPower (r + 2) s q.val =
      T.determinantComplexPower (r + 1) s (adjacentRankLowerLargeProjection q) *
        T.determinantComplexPower 1 s
          ((adjacentRankLowerShape r).oppositeLeviProjection F q 1) := by
  change T.unramifiedCharacter _ (GeneralLinear.determinant q.val) = _
  rw [adjacentRankLower_determinant, map_mul]
  rfl

end PadicCharacters

end Langlands.AllField.RankinSelberg

namespace Langlands.AllField.Shahidi
open Langlands.Shahidi hiding map_rectangularConj_padic
open Langlands.AllField.Shahidi

end Langlands.AllField.Shahidi

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement RankOneWhittakerTypeStatement TwoBlockWhittakerDeformationStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement adjacentRankDeterminantWeight adjacentRankDeterminantWeight_apply adjacentRankDeterminantWeight_locallyConstant adjacentRankLowerScalarProjection adjacentRankLower_determinantComplexPower adjacentRankLower_halfModulus adjacentRankLower_weightRatio isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt lastRowCompactOrbit normalizedAbsoluteValue normalizedAbsoluteValue_apply rankOneCharacter_isOfWhittakerType rankOneExtensionCharacter rankOneExtensionCharacter_isOfWhittakerType rankOneExtensionCharacter_isSmooth rankOneWhittakerType twoBlockDeformedBlocks twoBlockDeformedBlocks_zero twoBlockDeformedInduced
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory Matrix
open Langlands.HarmonicAnalysis hiding padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis

section Normalization

universe uF
variable {F : Type uF} [Field F]
  (T : LocalFieldData F) {r : ℕ}

/-- The scalar diagonal block, with its rank made explicit. -/
def adjacentRankLowerScalarProjection :
    (adjacentRankLowerShape r).oppositeParabolic F →*
      GeneralLinear 1 F where
  toFun q := (adjacentRankLowerShape r).oppositeLeviProjection F q 1
  map_one' := by simp; rfl
  map_mul' q q' := by simp; rfl

/-- The opposite half-modulus on the exact ordered lower shape. -/
theorem adjacentRankLower_halfModulus :
    T.oppositeParabolicHalfModulus (adjacentRankLowerShape r) =
      (T.determinantComplexPower (r + 1) (-1 / 2)).comp adjacentRankLowerLargeProjection *
        (T.determinantComplexPower 1 ((r + 1 : ℕ) / 2)).comp
          adjacentRankLowerScalarProjection := by
  let B := adjacentRankLowerShape r
  let a := adjacentRankLowerLargeProjection (K := F) (r := r)
  let d : B.oppositeParabolic F →* GeneralLinear 1 F :=
    adjacentRankLowerScalarProjection
  have hmod : (T.leviModulus B).comp (B.oppositeLeviProjection F) =
      (T.determinantNorm (r + 1)).comp a /
        ((T.determinantNorm 1).comp d) ^ (r + 1) := by
    apply MonoidHom.ext
    intro q
    change T.leviModulus B (B.oppositeLeviProjection F q) =
      T.determinantNorm (r + 1) (B.oppositeLeviProjection F q 0) /
        T.determinantNorm 1 (B.oppositeLeviProjection F q 1) ^ (r + 1)
    simpa only [pow_one] using
      T.leviModulus_twoBlocks (Nat.succ_pos r) (Nat.succ_pos 0)
      (B.oppositeLeviProjection F q)
  have hhalf : T.oppositeParabolicHalfModulus B =
      (Shahidi.complexPower
        ((T.leviModulus B).comp (B.oppositeLeviProjection F)) (1 / 2))⁻¹ := by
    rw [Shahidi.complexPower_comp, Shahidi.complexPower_half]
    rfl
  change T.oppositeParabolicHalfModulus B =
    (T.determinantComplexPower (r + 1) (-1 / 2)).comp a *
      (T.determinantComplexPower 1 ((r + 1 : ℕ) / 2)).comp d
  rw [hhalf, hmod]
  change (Shahidi.complexPower
    ((T.determinantNorm (r + 1)).comp a *
      (((T.determinantNorm 1).comp d) ^ (r + 1))⁻¹) (1 / 2))⁻¹ = _
  rw [Shahidi.complexPower_mul,
    Shahidi.complexPower_inv, Shahidi.complexPower_pow]
  simp only [T.determinantComplexPower_eq_complexPower, ← Shahidi.complexPower_comp]
  rw [show (-1 / 2 : ℂ) = -(1 / 2) by ring, Shahidi.complexPower_neg]
  apply MonoidHom.ext
  intro q
  simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, _root_.mul_inv_rev, inv_inv]
  rw [mul_comm]
  congr 2
  simp only [div_eq_mul_inv, one_mul]

/-- The two weights in JPSS (10) give exactly the lower normalized character. -/
theorem adjacentRankLower_weightRatio
    (χ : letI := T.topology; Quasicharacter F)
    (q : (adjacentRankLowerShape r).oppositeParabolic F) :
    letI := T.topology
    (adjacentRankDeterminantWeight T χ (r + 2) ((r + 1 : ℕ) / 2)).toMonoidHom q.val *
        ((adjacentRankDeterminantWeight T χ (r + 1) ((r + 2 : ℕ) / 2)).toMonoidHom
          (adjacentRankLowerLargeProjection q))⁻¹ =
      T.oppositeParabolicHalfModulus (adjacentRankLowerShape r) q *
        χ (GeneralLinear.determinant (adjacentRankLowerScalarProjection q)) := by
  let := T.topology
  have he : T.determinantComplexPower (r + 1) ((r + 2 : ℕ) / 2) =
      T.determinantComplexPower (r + 1) ((r + 1 : ℕ) / 2) *
        T.determinantComplexPower (r + 1) (1 / 2) := by
    rw [← T.determinantComplexPower_add]
    congr 1
    push_cast
    ring
  rw [adjacentRankDeterminantWeight_apply, adjacentRankDeterminantWeight_apply,
    adjacentRankLower_determinantComplexPower, adjacentRankLower_determinant, map_mul,
    adjacentRankLower_halfModulus, he]
  change _ =
    (T.determinantComplexPower (r + 1) (-1 / 2) (adjacentRankLowerLargeProjection q) *
      T.determinantComplexPower 1 ((r + 1 : ℕ) / 2) (adjacentRankLowerScalarProjection q)) *
      χ (GeneralLinear.determinant (adjacentRankLowerScalarProjection q))
  rw [show (-1 / 2 : ℂ) = -(1 / 2) by ring, T.determinantComplexPower_neg]
  simp only [MonoidHom.mul_apply, MonoidHom.inv_apply]
  have halg (x y z w t : ℂˣ) :
      (x * y) * (z * w) * (x * (z * t))⁻¹ = (t⁻¹ * w) * y := by
    apply Units.ext
    simp only [Units.val_mul, Units.val_inv_eq_inv_val]
    field_simp
  exact halg _ _ _ _ _

end Normalization

section TensorCoordinates


end TensorCoordinates

namespace Padic
open Langlands.RankinSelberg.Padic hiding adjacentRankLowerCompactRepresentation adjacentRankLowerInducingCoordinates adjacentRankLowerTensorCoordinates_action adjacentRankLowerTensorRepresentation adjacentRankNormalizedSection adjacentRankNormalizedSectionTensor adjacentRankNormalizedSectionTensor_tmul adjacentRankNormalizedSection_eval adjacentRankNormalizedSection_right adjacentSectionFieldTopology adjacentSectionGLBorel adjacentSectionGLMeasurable adjacentSectionLocalField adjacentSectionT2 adjacentSectionValuativeRel
open Langlands.AllField.RankinSelberg.Padic
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement RankOneWhittakerTypeStatement TwoBlockWhittakerDeformationStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement adjacentRankDeterminantWeight adjacentRankDeterminantWeight_apply adjacentRankDeterminantWeight_locallyConstant adjacentRankLowerScalarProjection adjacentRankLower_determinantComplexPower adjacentRankLower_halfModulus adjacentRankLower_weightRatio isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt lastRowCompactOrbit normalizedAbsoluteValue normalizedAbsoluteValue_apply rankOneCharacter_isOfWhittakerType rankOneExtensionCharacter rankOneExtensionCharacter_isOfWhittakerType rankOneExtensionCharacter_isSmooth rankOneWhittakerType twoBlockDeformedBlocks twoBlockDeformedBlocks_zero twoBlockDeformedInduced
open Langlands.AllField.RankinSelberg

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance adjacentSectionT2 : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance adjacentSectionGLMeasurable (n : ℕ) :
    MeasurableSpace (GeneralLinear (n + 1) F) := borel _
local instance adjacentSectionGLBorel (n : ℕ) :
    BorelSpace (GeneralLinear (n + 1) F) := ⟨rfl⟩

variable {r : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (σ : Representation ℂ (GeneralLinear (r + 1) F) V)
  (χ : Quasicharacter F)

/-- The host's block tensor action in original-module coordinates. -/
theorem adjacentRankLowerTensorCoordinates_action
    (m : (adjacentRankLowerShape r).Levi F)
    (z : PiTensorProduct ℂ (Shahidi.pairCarrier V (ULift.{uV} ℂ))) :
    adjacentRankLowerTensorCoordinates V
      ((adjacentRankLowerShape r).blockTensor
        (Shahidi.pairFamily σ (rankOneExtensionCharacter.{uF, uV} F χ)) m z) =
      (χ (GeneralLinear.determinant (m 1)) : ℂ) •
        σ (m 0) (adjacentRankLowerTensorCoordinates V z) := by
  obtain ⟨v, rfl⟩ := (adjacentRankLowerTensorCoordinates V).symm.surjective z
  rw [adjacentRankLowerTensorCoordinates_symm, Shahidi.blockTensor_pairTensor]
  rw [adjacentRankLowerTensorCoordinates_pairTensor,
    adjacentRankLowerTensorCoordinates_pairTensor]
  change ((χ (GeneralLinear.determinant (m 1)) : ℂ) * 1) • σ (m 0) v =
    (χ (GeneralLinear.determinant (m 1)) : ℂ) • σ (m 0) ((1 : ℂ) • v)
  simp only [mul_one, one_smul]

/-- The actual parabolic action obtained from the compact average. -/
abbrev adjacentRankLowerCompactRepresentation :
    Representation ℂ ((adjacentRankLowerShape r).oppositeParabolic F) V :=
  adjacentRankCompactSectionRepresentation
    ((adjacentRankLowerShape r).oppositeParabolic F)
    adjacentRankLowerLargeProjection σ
    (adjacentRankDeterminantWeight (⟨⟩ : LocalFieldData F) χ
      (r + 1) ((r + 2 : ℕ) / 2)).toMonoidHom
    (adjacentRankDeterminantWeight (⟨⟩ : LocalFieldData F) χ
      (r + 2) ((r + 1 : ℕ) / 2))

/-- The exact tensor-valued inducing representation in the host target. -/
abbrev adjacentRankLowerTensorRepresentation :=
  Langlands.twist
    ((⟨⟩ : LocalFieldData F).oppositeParabolicHalfModulus (adjacentRankLowerShape r))
    (((adjacentRankLowerShape r).blockTensor
      (Shahidi.pairFamily σ (rankOneExtensionCharacter.{uF, uV} F χ))).comp
        ((adjacentRankLowerShape r).oppositeLeviProjection F))

/-- Original-module coordinates identify the compact-section action with the
host's normalized inducing action. -/
def adjacentRankLowerInducingCoordinates :
    (adjacentRankLowerTensorRepresentation F σ χ).Equiv
      (adjacentRankLowerCompactRepresentation F σ χ) :=
  Representation.Equiv.mk (adjacentRankLowerTensorCoordinates V) (by
    intro q
    apply LinearMap.ext
    intro z
    change adjacentRankLowerTensorCoordinates V
        (((⟨⟩ : LocalFieldData F).oppositeParabolicHalfModulus
          (adjacentRankLowerShape r) q : ℂ) •
          (adjacentRankLowerShape r).blockTensor
            (Shahidi.pairFamily σ (rankOneExtensionCharacter.{uF, uV} F χ))
              ((adjacentRankLowerShape r).oppositeLeviProjection F q) z) =
      (((adjacentRankDeterminantWeight (⟨⟩ : LocalFieldData F) χ
          (r + 2) ((r + 1 : ℕ) / 2)).toMonoidHom q.val *
        ((adjacentRankDeterminantWeight (⟨⟩ : LocalFieldData F) χ
          (r + 1) ((r + 2 : ℕ) / 2)).toMonoidHom
            (adjacentRankLowerLargeProjection q))⁻¹ : ℂˣ) : ℂ) •
          σ (adjacentRankLowerLargeProjection q)
            (adjacentRankLowerTensorCoordinates V z)
    rw [map_smul, adjacentRankLowerTensorCoordinates_action, smul_smul,
      adjacentRankLower_weightRatio]
    rfl)

/-- The compact full-rank section in the exact canonical normalized lower induction. -/
def adjacentRankNormalizedSection (hσ : IsSmooth σ)
    (Φ : adjacentRankCompactTests (r + 1) F) (v : V) :
    ((⟨⟩ : LocalFieldData F).normalizedOppositeParabolicInduced (adjacentRankLowerShape r)
      ((adjacentRankLowerShape r).blockTensor
        (Shahidi.pairFamily σ (rankOneExtensionCharacter.{uF, uV} F χ)))).asModule :=
  Induction.smoothInducedMap
    ((adjacentRankLowerShape r).oppositeParabolic F)
    (adjacentRankLowerInducingCoordinates F σ χ).symm.toIntertwiningMap
    (adjacentRankCompactSection (generalLinearHaar F r) σ hσ
      (adjacentRankDeterminantWeight (⟨⟩ : LocalFieldData F) χ
        (r + 1) ((r + 2 : ℕ) / 2)).toMonoidHom
      (adjacentRankDeterminantWeight_locallyConstant (⟨⟩ : LocalFieldData F) χ
        (r + 1) ((r + 2 : ℕ) / 2))
      (adjacentRankDeterminantWeight (⟨⟩ : LocalFieldData F) χ
        (r + 2) ((r + 1 : ℕ) / 2))
      ((adjacentRankLowerShape r).oppositeParabolic F)
      adjacentRankLowerLargeProjection adjacentRankLower_rectangular_mul
      (fun q => measurePreserving_mul_right (generalLinearHaar F r)
        (adjacentRankLowerLargeProjection q)) Φ v)

/-- Evaluation retains the literal compact-average formula on the original module. -/
@[simp] theorem adjacentRankNormalizedSection_eval (hσ : IsSmooth σ)
    (Φ : adjacentRankCompactTests (r + 1) F) (v : V)
    (g : GeneralLinear (r + 2) F) :
    Induction.eval ((adjacentRankLowerShape r).oppositeParabolic F)
      (adjacentRankLowerTensorRepresentation F σ χ)
      (adjacentRankNormalizedSection F σ χ hσ Φ v) g =
      Shahidi.pairTensor
        (((adjacentRankDeterminantWeight (⟨⟩ : LocalFieldData F) χ
          (r + 2) ((r + 1 : ℕ) / 2)).toMonoidHom g : ℂ) •
          adjacentRankCompactAverage (generalLinearHaar F r) σ hσ
            (adjacentRankDeterminantWeight (⟨⟩ : LocalFieldData F) χ
              (r + 1) ((r + 2 : ℕ) / 2)).toMonoidHom
            (adjacentRankDeterminantWeight_locallyConstant (⟨⟩ : LocalFieldData F) χ
              (r + 1) ((r + 2 : ℕ) / 2)) Φ v g)
        (ULift.up 1) := by
  change (adjacentRankLowerTensorCoordinates V).symm _ = _
  exact adjacentRankLowerTensorCoordinates_symm _ _

/-- The normalized section map on the full compact-test/original-vector tensor product. -/
def adjacentRankNormalizedSectionTensor (hσ : IsSmooth σ) :
    TensorProduct ℂ (adjacentRankCompactTests (r + 1) F) V →ₗ[ℂ]
      ((⟨⟩ : LocalFieldData F).normalizedOppositeParabolicInduced (adjacentRankLowerShape r)
        ((adjacentRankLowerShape r).blockTensor
          (Shahidi.pairFamily σ (rankOneExtensionCharacter.{uF, uV} F χ)))).asModule :=
  (Induction.smoothInducedMap
    ((adjacentRankLowerShape r).oppositeParabolic F)
    (adjacentRankLowerInducingCoordinates F σ χ).symm.toIntertwiningMap).toLinearMap.comp
    (adjacentRankCompactSectionTensor (generalLinearHaar F r) σ hσ
      (adjacentRankDeterminantWeight (⟨⟩ : LocalFieldData F) χ
        (r + 1) ((r + 2 : ℕ) / 2)).toMonoidHom
      (adjacentRankDeterminantWeight_locallyConstant (⟨⟩ : LocalFieldData F) χ
        (r + 1) ((r + 2 : ℕ) / 2))
      (adjacentRankDeterminantWeight (⟨⟩ : LocalFieldData F) χ
        (r + 2) ((r + 1 : ℕ) / 2))
      ((adjacentRankLowerShape r).oppositeParabolic F)
      adjacentRankLowerLargeProjection adjacentRankLower_rectangular_mul
      (fun q => measurePreserving_mul_right (generalLinearHaar F r)
        (adjacentRankLowerLargeProjection q)))

@[simp] theorem adjacentRankNormalizedSectionTensor_tmul (hσ : IsSmooth σ)
    (Φ : adjacentRankCompactTests (r + 1) F) (v : V) :
    adjacentRankNormalizedSectionTensor F σ χ hσ (Φ ⊗ₜ[ℂ] v) =
      adjacentRankNormalizedSection F σ χ hσ Φ v := rfl

/-- The exact induced action has the weighted test-translation formula. -/
theorem adjacentRankNormalizedSection_right (hσ : IsSmooth σ)
    (Φ : adjacentRankCompactTests (r + 1) F) (v : V)
    (k : GeneralLinear (r + 2) F) :
    (⟨⟩ : LocalFieldData F).normalizedOppositeParabolicInduced (adjacentRankLowerShape r)
      ((adjacentRankLowerShape r).blockTensor
        (Shahidi.pairFamily σ (rankOneExtensionCharacter.{uF, uV} F χ))) k
      (adjacentRankNormalizedSection F σ χ hσ Φ v) =
      ((adjacentRankDeterminantWeight (⟨⟩ : LocalFieldData F) χ
        (r + 2) ((r + 1 : ℕ) / 2)).toMonoidHom k : ℂ) •
        adjacentRankNormalizedSection F σ χ hσ
          (adjacentRankCompactTestTranslate k Φ) v := by
  let ξ := (adjacentRankDeterminantWeight (⟨⟩ : LocalFieldData F) χ
    (r + 1) ((r + 2 : ℕ) / 2)).toMonoidHom
  let hξ := adjacentRankDeterminantWeight_locallyConstant (⟨⟩ : LocalFieldData F) χ
    (r + 1) ((r + 2 : ℕ) / 2)
  let θ := adjacentRankDeterminantWeight (⟨⟩ : LocalFieldData F) χ
    (r + 2) ((r + 1 : ℕ) / 2)
  apply Subtype.ext
  apply Subtype.ext
  funext g
  change (adjacentRankLowerTensorCoordinates V).symm
      (adjacentRankCompactSectionValue (generalLinearHaar F r)
        σ hσ ξ hξ θ Φ v (g * k)) =
    (θ.toMonoidHom k : ℂ) • (adjacentRankLowerTensorCoordinates V).symm
      (adjacentRankCompactSectionValue (generalLinearHaar F r)
        σ hσ ξ hξ θ (adjacentRankCompactTestTranslate k Φ) v g)
  rw [adjacentRankCompactSectionValue_right, map_smul]

end Padic

end Langlands.AllField.RankinSelberg
