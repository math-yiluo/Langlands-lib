import Langlands.Representation.RankinSelberg.AdjacentRankLowerParabolic
import Langlands.Representation.RankinSelberg.AdjacentRankCompactSection
import Langlands.Representation.RankinSelberg.RankOneExtensionCharacter
import Langlands.Representation.Shahidi.TensorBridge
import Langlands.Representation.Induction.OppositeParabolic
import Langlands.Representation.Twist.ContinuousCharacterProof
import Langlands.Representation.RankinSelberg.GeneralLinearUnimodularity

/-! Compact-orbit sections in the exact normalized adjacent-rank lower induction. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

open scoped BigOperators TensorProduct NNReal

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Matrix

universe uF uV

section PadicCharacters

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData)

/-- The smooth determinant weight `χ(det g) |det g|^s`. -/
def adjacentRankDeterminantWeight
    (χ : letI := T.topology; Quasicharacter F.Carrier) (n : ℕ) (s : ℂ) :
    letI := T.topology
    Induction.SmoothCharacter ℂ (GeneralLinear n F.Carrier) := by
  letI := T.topology
  letI := T.generalLinearNonarchimedean n
  refine ⟨(χ : F.Carrierˣ →* ℂˣ).comp GeneralLinear.determinant *
    T.determinantComplexPower n s, ?_⟩
  apply isOpen_ker_of_continuous_complex_character
  change Continuous (fun g : GeneralLinear n F.Carrier =>
    χ (GeneralLinear.determinant g) *
      T.unramifiedCharacter
        (LocalFactor.spectralParameter T.residueCardinality T.residueCardinality_real_pos s)
        (GeneralLinear.determinant g))
  exact (χ.continuous.mul (T.continuous_unramifiedCharacter _)).comp
    (T.generalLinearDeterminant n).continuous

@[simp] theorem adjacentRankDeterminantWeight_apply
    (χ : letI := T.topology; Quasicharacter F.Carrier) (n : ℕ) (s : ℂ)
    (g : GeneralLinear n F.Carrier) :
    letI := T.topology
    (adjacentRankDeterminantWeight T χ n s).toMonoidHom g =
      χ (GeneralLinear.determinant g) * T.determinantComplexPower n s g := rfl

/-- The scalar inner weight is locally constant on the actual general linear group. -/
theorem adjacentRankDeterminantWeight_locallyConstant
    (χ : letI := T.topology; Quasicharacter F.Carrier) (n : ℕ) (s : ℂ) :
    letI := T.topology
    IsLocallyConstant (fun g : GeneralLinear n F.Carrier =>
      ((adjacentRankDeterminantWeight T χ n s).toMonoidHom g : ℂ)) := by
  let := T.topology
  let := T.generalLinearNonarchimedean n
  apply isLocallyConstant_of_continuous_complex_character
  exact (χ.continuous.mul (T.continuous_unramifiedCharacter _)).comp
    (T.generalLinearDeterminant n).continuous

/-- The actual determinant power splits over the two lower diagonal blocks. -/
theorem adjacentRankLower_determinantComplexPower {r : ℕ}
    (q : (adjacentRankLowerShape r).oppositeParabolic F.Carrier) (s : ℂ) :
    T.determinantComplexPower (r + 2) s q.val =
      T.determinantComplexPower (r + 1) s (adjacentRankLowerLargeProjection q) *
        T.determinantComplexPower 1 s
          ((adjacentRankLowerShape r).oppositeLeviProjection F.Carrier q 1) := by
  change T.unramifiedCharacter _ (GeneralLinear.determinant q.val) = _
  rw [adjacentRankLower_determinant, map_mul]
  rfl

end PadicCharacters

end Langlands.RankinSelberg

namespace Langlands.Shahidi

/-- Complex powers commute with pullback of positive characters. -/
theorem complexPower_comp {G H : Type*} [Group G] [Group H]
    (δ : H →* ℝ≥0ˣ) (f : G →* H) (s : ℂ) :
    complexPower (δ.comp f) s = (complexPower δ s).comp f := by
  ext g
  rfl

end Langlands.Shahidi

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Matrix

section Normalization

universe uF
variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {r : ℕ}

/-- The scalar diagonal block, with its rank made explicit. -/
def adjacentRankLowerScalarProjection :
    (adjacentRankLowerShape r).oppositeParabolic F.Carrier →*
      GeneralLinear 1 F.Carrier where
  toFun q := (adjacentRankLowerShape r).oppositeLeviProjection F.Carrier q 1
  map_one' := by simp; rfl
  map_mul' q q' := by simp; rfl

/-- The opposite half-modulus on the exact ordered lower shape. -/
theorem adjacentRankLower_halfModulus :
    T.oppositeParabolicHalfModulus (adjacentRankLowerShape r) =
      (T.determinantComplexPower (r + 1) (-1 / 2)).comp adjacentRankLowerLargeProjection *
        (T.determinantComplexPower 1 ((r + 1 : ℕ) / 2)).comp
          adjacentRankLowerScalarProjection := by
  let B := adjacentRankLowerShape r
  let a := adjacentRankLowerLargeProjection (K := F.Carrier) (r := r)
  let d : B.oppositeParabolic F.Carrier →* GeneralLinear 1 F.Carrier :=
    adjacentRankLowerScalarProjection
  have hmod : (T.leviModulus B).comp (B.oppositeLeviProjection F.Carrier) =
      (T.determinantNorm (r + 1)).comp a /
        ((T.determinantNorm 1).comp d) ^ (r + 1) := by
    apply MonoidHom.ext
    intro q
    change T.leviModulus B (B.oppositeLeviProjection F.Carrier q) =
      T.determinantNorm (r + 1) (B.oppositeLeviProjection F.Carrier q 0) /
        T.determinantNorm 1 (B.oppositeLeviProjection F.Carrier q 1) ^ (r + 1)
    simpa only [pow_one] using
      T.leviModulus_twoBlocks (Nat.succ_pos r) (Nat.succ_pos 0)
      (B.oppositeLeviProjection F.Carrier q)
  have hhalf : T.oppositeParabolicHalfModulus B =
      (Shahidi.complexPower
        ((T.leviModulus B).comp (B.oppositeLeviProjection F.Carrier)) (1 / 2))⁻¹ := by
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
    (χ : letI := T.topology; Quasicharacter F.Carrier)
    (q : (adjacentRankLowerShape r).oppositeParabolic F.Carrier) :
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

variable (V : Type uV) [AddCommGroup V] [Module ℂ V]

/-- The original module, in the exact lifted scalar tensor coordinates of the host. -/
def adjacentRankLowerTensorCoordinates :
    PiTensorProduct ℂ (Shahidi.pairCarrier V (ULift.{uV} ℂ)) ≃ₗ[ℂ] V :=
  (Shahidi.pairTensorEquiv V (ULift.{uV} ℂ)).trans
    ((TensorProduct.congr (LinearEquiv.refl ℂ V) ULift.moduleEquiv).trans
      (TensorProduct.rid ℂ V))

@[simp] theorem adjacentRankLowerTensorCoordinates_pairTensor
    (v : V) (z : ULift.{uV} ℂ) :
    adjacentRankLowerTensorCoordinates V (Shahidi.pairTensor v z) = z.down • v := by
  simp [adjacentRankLowerTensorCoordinates]

@[simp] theorem adjacentRankLowerTensorCoordinates_symm
    (v : V) :
    (adjacentRankLowerTensorCoordinates V).symm v =
      Shahidi.pairTensor v (ULift.up 1) := by
  apply (adjacentRankLowerTensorCoordinates V).injective
  simp

end TensorCoordinates

namespace Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance adjacentSectionFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance adjacentSectionValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance adjacentSectionLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance adjacentSectionT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance adjacentSectionGLMeasurable (n : ℕ) :
    MeasurableSpace (GeneralLinear (n + 1) F.Carrier) := borel _
local instance adjacentSectionGLBorel (n : ℕ) :
    BorelSpace (GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩

variable {r : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (σ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
  (χ : Quasicharacter F.Carrier)

/-- The host's block tensor action in original-module coordinates. -/
theorem adjacentRankLowerTensorCoordinates_action
    (m : (adjacentRankLowerShape r).Levi F.Carrier)
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
    Representation ℂ ((adjacentRankLowerShape r).oppositeParabolic F.Carrier) V :=
  adjacentRankCompactSectionRepresentation
    ((adjacentRankLowerShape r).oppositeParabolic F.Carrier)
    adjacentRankLowerLargeProjection σ
    (adjacentRankDeterminantWeight F.canonicalTopologicalData χ
      (r + 1) ((r + 2 : ℕ) / 2)).toMonoidHom
    (adjacentRankDeterminantWeight F.canonicalTopologicalData χ
      (r + 2) ((r + 1 : ℕ) / 2))

/-- The exact tensor-valued inducing representation in the host target. -/
abbrev adjacentRankLowerTensorRepresentation :=
  Langlands.twist
    (F.canonicalTopologicalData.oppositeParabolicHalfModulus (adjacentRankLowerShape r))
    (((adjacentRankLowerShape r).blockTensor
      (Shahidi.pairFamily σ (rankOneExtensionCharacter.{uF, uV} F χ))).comp
        ((adjacentRankLowerShape r).oppositeLeviProjection F.Carrier))

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
        ((F.canonicalTopologicalData.oppositeParabolicHalfModulus
          (adjacentRankLowerShape r) q : ℂ) •
          (adjacentRankLowerShape r).blockTensor
            (Shahidi.pairFamily σ (rankOneExtensionCharacter.{uF, uV} F χ))
              ((adjacentRankLowerShape r).oppositeLeviProjection F.Carrier q) z) =
      (((adjacentRankDeterminantWeight F.canonicalTopologicalData χ
          (r + 2) ((r + 1 : ℕ) / 2)).toMonoidHom q.val *
        ((adjacentRankDeterminantWeight F.canonicalTopologicalData χ
          (r + 1) ((r + 2 : ℕ) / 2)).toMonoidHom
            (adjacentRankLowerLargeProjection q))⁻¹ : ℂˣ) : ℂ) •
          σ (adjacentRankLowerLargeProjection q)
            (adjacentRankLowerTensorCoordinates V z)
    rw [map_smul, adjacentRankLowerTensorCoordinates_action, smul_smul,
      adjacentRankLower_weightRatio]
    rfl)

/-- The compact full-rank section in the exact canonical normalized lower induction. -/
def adjacentRankNormalizedSection (hσ : IsSmooth σ)
    (Φ : adjacentRankCompactTests (r + 1) F.Carrier) (v : V) :
    (F.canonicalNormalizedOppositeParabolicInduced (adjacentRankLowerShape r)
      ((adjacentRankLowerShape r).blockTensor
        (Shahidi.pairFamily σ (rankOneExtensionCharacter.{uF, uV} F χ)))).asModule :=
  Induction.smoothInducedMap
    ((adjacentRankLowerShape r).oppositeParabolic F.Carrier)
    (adjacentRankLowerInducingCoordinates F σ χ).symm.toIntertwiningMap
    (adjacentRankCompactSection (generalLinearHaar F.Carrier r) σ hσ
      (adjacentRankDeterminantWeight F.canonicalTopologicalData χ
        (r + 1) ((r + 2 : ℕ) / 2)).toMonoidHom
      (adjacentRankDeterminantWeight_locallyConstant F.canonicalTopologicalData χ
        (r + 1) ((r + 2 : ℕ) / 2))
      (adjacentRankDeterminantWeight F.canonicalTopologicalData χ
        (r + 2) ((r + 1 : ℕ) / 2))
      ((adjacentRankLowerShape r).oppositeParabolic F.Carrier)
      adjacentRankLowerLargeProjection adjacentRankLower_rectangular_mul
      (fun q => measurePreserving_mul_right (generalLinearHaar F.Carrier r)
        (adjacentRankLowerLargeProjection q)) Φ v)

/-- Evaluation retains the literal compact-average formula on the original module. -/
@[simp] theorem adjacentRankNormalizedSection_eval (hσ : IsSmooth σ)
    (Φ : adjacentRankCompactTests (r + 1) F.Carrier) (v : V)
    (g : GeneralLinear (r + 2) F.Carrier) :
    Induction.eval ((adjacentRankLowerShape r).oppositeParabolic F.Carrier)
      (adjacentRankLowerTensorRepresentation F σ χ)
      (adjacentRankNormalizedSection F σ χ hσ Φ v) g =
      Shahidi.pairTensor
        (((adjacentRankDeterminantWeight F.canonicalTopologicalData χ
          (r + 2) ((r + 1 : ℕ) / 2)).toMonoidHom g : ℂ) •
          adjacentRankCompactAverage (generalLinearHaar F.Carrier r) σ hσ
            (adjacentRankDeterminantWeight F.canonicalTopologicalData χ
              (r + 1) ((r + 2 : ℕ) / 2)).toMonoidHom
            (adjacentRankDeterminantWeight_locallyConstant F.canonicalTopologicalData χ
              (r + 1) ((r + 2 : ℕ) / 2)) Φ v g)
        (ULift.up 1) := by
  change (adjacentRankLowerTensorCoordinates V).symm _ = _
  exact adjacentRankLowerTensorCoordinates_symm _ _

/-- The normalized section map on the full compact-test/original-vector tensor product. -/
def adjacentRankNormalizedSectionTensor (hσ : IsSmooth σ) :
    TensorProduct ℂ (adjacentRankCompactTests (r + 1) F.Carrier) V →ₗ[ℂ]
      (F.canonicalNormalizedOppositeParabolicInduced (adjacentRankLowerShape r)
        ((adjacentRankLowerShape r).blockTensor
          (Shahidi.pairFamily σ (rankOneExtensionCharacter.{uF, uV} F χ)))).asModule :=
  (Induction.smoothInducedMap
    ((adjacentRankLowerShape r).oppositeParabolic F.Carrier)
    (adjacentRankLowerInducingCoordinates F σ χ).symm.toIntertwiningMap).toLinearMap.comp
    (adjacentRankCompactSectionTensor (generalLinearHaar F.Carrier r) σ hσ
      (adjacentRankDeterminantWeight F.canonicalTopologicalData χ
        (r + 1) ((r + 2 : ℕ) / 2)).toMonoidHom
      (adjacentRankDeterminantWeight_locallyConstant F.canonicalTopologicalData χ
        (r + 1) ((r + 2 : ℕ) / 2))
      (adjacentRankDeterminantWeight F.canonicalTopologicalData χ
        (r + 2) ((r + 1 : ℕ) / 2))
      ((adjacentRankLowerShape r).oppositeParabolic F.Carrier)
      adjacentRankLowerLargeProjection adjacentRankLower_rectangular_mul
      (fun q => measurePreserving_mul_right (generalLinearHaar F.Carrier r)
        (adjacentRankLowerLargeProjection q)))

@[simp] theorem adjacentRankNormalizedSectionTensor_tmul (hσ : IsSmooth σ)
    (Φ : adjacentRankCompactTests (r + 1) F.Carrier) (v : V) :
    adjacentRankNormalizedSectionTensor F σ χ hσ (Φ ⊗ₜ[ℂ] v) =
      adjacentRankNormalizedSection F σ χ hσ Φ v := rfl

/-- The exact induced action has the weighted test-translation formula. -/
theorem adjacentRankNormalizedSection_right (hσ : IsSmooth σ)
    (Φ : adjacentRankCompactTests (r + 1) F.Carrier) (v : V)
    (k : GeneralLinear (r + 2) F.Carrier) :
    F.canonicalNormalizedOppositeParabolicInduced (adjacentRankLowerShape r)
      ((adjacentRankLowerShape r).blockTensor
        (Shahidi.pairFamily σ (rankOneExtensionCharacter.{uF, uV} F χ))) k
      (adjacentRankNormalizedSection F σ χ hσ Φ v) =
      ((adjacentRankDeterminantWeight F.canonicalTopologicalData χ
        (r + 2) ((r + 1 : ℕ) / 2)).toMonoidHom k : ℂ) •
        adjacentRankNormalizedSection F σ χ hσ
          (adjacentRankCompactTestTranslate k Φ) v := by
  let ξ := (adjacentRankDeterminantWeight F.canonicalTopologicalData χ
    (r + 1) ((r + 2 : ℕ) / 2)).toMonoidHom
  let hξ := adjacentRankDeterminantWeight_locallyConstant F.canonicalTopologicalData χ
    (r + 1) ((r + 2 : ℕ) / 2)
  let θ := adjacentRankDeterminantWeight F.canonicalTopologicalData χ
    (r + 2) ((r + 1 : ℕ) / 2)
  apply Subtype.ext
  apply Subtype.ext
  funext g
  change (adjacentRankLowerTensorCoordinates V).symm
      (adjacentRankCompactSectionValue (generalLinearHaar F.Carrier r)
        σ hσ ξ hξ θ Φ v (g * k)) =
    (θ.toMonoidHom k : ℂ) • (adjacentRankLowerTensorCoordinates V).symm
      (adjacentRankCompactSectionValue (generalLinearHaar F.Carrier r)
        σ hσ ξ hξ θ (adjacentRankCompactTestTranslate k Φ) v g)
  rw [adjacentRankCompactSectionValue_right, map_smul]

end Padic

end Langlands.RankinSelberg
