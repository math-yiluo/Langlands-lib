import Langlands.Global.AdelicBlockCompactEmbedding
import Langlands.Global.AdelicBlockCoefficientTensor
import Langlands.Global.AdelicBlockScalarSectionActions
import Langlands.Representation.Tensor.Finite

/-!
# Evaluation of the actual adelic block section at a finite compact point

Restrict the scalar function to a normalized Levi slice with infinite
coordinate one, and transport that slice back to the tensor of the block
realizations. Conjugation by the finite compact point gives its coefficient
finite level; block diagonal inclusion gives its compact equivariance.
-/

noncomputable section

open scoped TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

namespace Langlands.Global.AdelicBlockScalarSections

open Langlands.Automorphic Langlands.GeneralLinear
open AdelicBlockParabolic AdelicBlockDeterminantCharacter PrimitiveAdelicHeight

variable (F : Type u) [Field F] [NumberField F] {n : ℕ} (B : BlockShape n)
  (S : ∀ i : Fin B.length, OperatorRealization F (B.size i))

local notation "Kf" => OpenSubgroup.toSubgroup (FiniteAdelicGL.standardIntegral F n)
local notation "K" => (standardCompact F n)
local notation "M" => FullLevi F B
local notation "V" => RealizedSections F B S
local notation "W" => coefficientValues F B S

local instance blockSliceEvaluationRationalAddCommGroup (t : ℕ) : AddCommGroup (RationalInvariantFunctions F t) := Submodule.addCommGroup _
local instance blockSliceEvaluationContinuousAddCommGroup (t : ℕ) : AddCommGroup (ContinuousRationalFunctions F t) := Submodule.addCommGroup _
local instance blockSliceEvaluationFiniteSmoothAddCommGroup (t : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions F t) :=
  Submodule.addCommGroup _
local instance blockSliceEvaluationAutomorphicAddCommGroup (t : ℕ) : AddCommGroup (AutomorphicForms F t) := Submodule.addCommGroup _
local instance blockSliceEvaluationStableAddCommGroup (t : ℕ) : AddCommGroup (StableAutomorphicFunctions F t) := Submodule.addCommGroup _
local instance blockSliceEvaluationRealizationAddCommGroup {t : ℕ} (T : OperatorRealization F t) : AddCommGroup T.Space :=
  Submodule.addCommGroup _

/-- The finite coefficient action is the product of the realized block actions. -/
abbrev coefficientFiniteAction :
    Representation ℂ (FiniteLevi F B) (⨂[ℂ] i, (S i).Space) :=
  FiniteTensor.external (fun i => (S i).finiteRepresentation)

/-- The infinite compact coefficient action is the product of the block compact actions. -/
abbrev coefficientInfiniteCompactAction : Representation ℂ
    (∀ i : Fin B.length, standardInfiniteCompact F (B.size i)) (⨂[ℂ] i, (S i).Space) :=
  FiniteTensor.external (fun i => (S i).compactRepresentation)

/-- A finite compact element gives a full compact point with infinite coordinate one. -/
def finiteSlicePoint (x : Kf) : K :=
  ⟨AdelicGL.ofFinite F n x.val, (mem_standardCompact_iff F n _).mpr
    ⟨by rw [AdelicGL.ofFinite_eq_pair, AdelicGL.infinite_pair]; exact one_mem _,
      by rw [AdelicGL.ofFinite_eq_pair, AdelicGL.finite_pair]; exact x.property⟩⟩

@[simp]
theorem finiteSlicePoint_val (x : Kf) : (finiteSlicePoint F x).val =
    AdelicGL.ofFinite F n x.val := rfl

/-- The normalized slice followed by the inverse of the coefficient equivalence. -/
def finiteSliceEvaluation (x : Kf) : V →ₗ[ℂ] (⨂[ℂ] i, (S i).Space) :=
  (coefficientEquiv F B S).symm.toLinearMap ∘ₗ {
    toFun := fun f => ⟨normalizedSlice F B f.val (finiteSlicePoint F x), f.property.2 _⟩
    map_add' := fun _ _ => Subtype.ext (funext fun _ => mul_add _ _ _)
    map_smul' := fun _ _ => Subtype.ext (funext fun _ => mul_left_comm _ _ _) }

@[simp]
theorem coefficientEvaluation_finiteSliceEvaluation (x : Kf) (f : V) :
    coefficientEvaluation F B S (finiteSliceEvaluation F B S x f) =
      normalizedSlice F B f.val (finiteSlicePoint F x) := by
  exact congrArg Subtype.val ((coefficientEquiv F B S).apply_symm_apply
    ⟨normalizedSlice F B f.val (finiteSlicePoint F x), f.property.2 _⟩)

/-- A conjugated block diagonal image in the finite ambient group. -/
def conjugateFiniteLevi (x : Kf) : FiniteLevi F B →ₜ* FiniteAdelicGL F n where
  toMonoidHom := (MulAut.conj x.val⁻¹).toMonoidHom.comp (B.leviEmbedding (FiniteAdeles F))
  continuous_toFun := by
    change Continuous fun d => x.val⁻¹ * B.leviEmbedding (FiniteAdeles F) d * x.val⁻¹⁻¹
    exact (continuous_const.mul (B.leviEmbeddingContinuous (FiniteAdeles F)).continuous).mul_const _

@[simp]
theorem conjugateFiniteLevi_apply (x : Kf) (d : FiniteLevi F B) :
    conjugateFiniteLevi F B x d = x.val⁻¹ * B.leviEmbedding (FiniteAdeles F) d * x.val := by
  change x.val⁻¹ * B.leviEmbedding (FiniteAdeles F) d * x.val⁻¹⁻¹ = _
  rw [inv_inv]

/-- The coefficient level is the inverse image of the ambient level intersected
with the finite compact, under the map conjugated by the inverse slice point. -/
def finiteSliceLevel (L : OpenSubgroup (FiniteAdelicGL F n)) (x : Kf) :
    OpenSubgroup (FiniteLevi F B) :=
  OpenSubgroup.comap (conjugateFiniteLevi F B x).toMonoidHom
    (conjugateFiniteLevi F B x).continuous (L ⊓ FiniteAdelicGL.standardIntegral F n)

/-- Evaluation at a finite compact point carries level-fixed vectors to vectors
fixed by the corresponding coefficient level. -/
theorem finiteSliceEvaluation_mem_fixedVectors (L : OpenSubgroup (FiniteAdelicGL F n))
    (x : Kf) (f : V) (hf : f ∈ fixedVectors (RealizedSections.finiteAction F B S) L.toSubgroup) :
    finiteSliceEvaluation F B S x f ∈ fixedVectors (coefficientFiniteAction F B S)
      (finiteSliceLevel F B L x).toSubgroup := by
  intro d
  let y := B.leviEmbedding (FiniteAdeles F) d.val
  let z := conjugateFiniteLevi F B x d.val
  have hz : z ∈ L ∧ z ∈ Kf := d.property
  have hax : x.val * z = y * x.val := by
    simp [z, y, ← mul_assoc]
  have hy : y ∈ Kf := by
    have h := congrArg (fun a : FiniteAdelicGL F n => a * x.val⁻¹) hax
    change (x.val * z) * x.val⁻¹ = (y * x.val) * x.val⁻¹ at h
    rw [mul_assoc y, mul_inv_cancel, mul_one] at h
    rw [← h]
    exact Subgroup.mul_mem Kf (Subgroup.mul_mem Kf x.property hz.2)
      (Subgroup.inv_mem Kf x.property)
  let p := B.leviInParabolic (Adeles F) (leviPair F B 1 d.val)
  have hpy : p.val = AdelicGL.ofFinite F n y := leviEmbedding_finiteOnly B F d.val
  have hp : p.val ∈ K := by
    rw [hpy]
    exact (finiteSlicePoint F ⟨y, hy⟩).property
  have hfactor : (finiteSlicePoint F x).val * AdelicGL.ofFinite F n z =
      p.val * (finiteSlicePoint F x).val := by
    rw [finiteSlicePoint_val, hpy, ← map_mul, ← map_mul, hax]
  have hfz : RealizedSections.finiteAction F B S z f = f := hf ⟨z, hz.1⟩
  apply coefficientEvaluation_injective F B S
  funext m
  change coefficientEvaluation F B S (PiTensorProduct.map (fun i =>
      (S i).finiteRepresentation (d.val i)) (finiteSliceEvaluation F B S x f)) m = _
  rw [coefficientEvaluation_finite, coefficientEvaluation_finiteSliceEvaluation]
  have h := normalizedSlice_rightTranslate F B f _ _ _ p hfactor m
  change normalizedSlice F B (RealizedSections.finiteAction F B S z f).val
    (finiteSlicePoint F x) m = _ at h
  rw [hfz, parabolicHalfCharacter_eq_one_of_mem_standardCompact B F p hp, Units.val_one,
    one_mul, B.leviProjection_section] at h
  exact h.symm

/-- Evaluation intertwines the infinite compact actions along block diagonal inclusion. -/
theorem finiteSliceEvaluation_infiniteCompact (x : Kf)
    (k : ∀ i : Fin B.length, standardInfiniteCompact F (B.size i)) (f : V) :
    finiteSliceEvaluation F B S x
      (RealizedSections.infiniteCompactAction F B S (infiniteLeviCompactInclusion B F k) f) =
    coefficientInfiniteCompactAction F B S k (finiteSliceEvaluation F B S x f) := by
  let a : InfiniteLevi F B := fun i => (k i).val
  let Kk := infiniteLeviCompactInclusion B F k
  let p := B.leviInParabolic (Adeles F) (leviPair F B a 1)
  have hpk : p.val = AdelicGL.ofInfinite F n Kk.val := leviEmbedding_infiniteOnly B F a
  have hp : p.val ∈ K := by
    rw [hpk]
    exact (infiniteCompactInclusion F Kk).property
  have hfactor : (finiteSlicePoint F x).val * AdelicGL.ofInfinite F n Kk.val =
      p.val * (finiteSlicePoint F x).val := by
    rw [finiteSlicePoint_val, hpk]
    exact (AdelicGL.ofFinite_commute_ofInfinite F n x.val Kk.val).eq
  apply coefficientEvaluation_injective F B S
  funext m
  change coefficientEvaluation F B S (finiteSliceEvaluation F B S x
      (RealizedSections.infiniteCompactAction F B S Kk f)) m =
    coefficientEvaluation F B S (PiTensorProduct.map (fun i =>
      (S i).compactRepresentation (k i)) (finiteSliceEvaluation F B S x f)) m
  rw [coefficientEvaluation_compact, coefficientEvaluation_finiteSliceEvaluation,
    coefficientEvaluation_finiteSliceEvaluation]
  have h := normalizedSlice_rightTranslate F B f _ _ _ p hfactor m
  change normalizedSlice F B (RealizedSections.infiniteCompactAction F B S Kk f).val
    (finiteSlicePoint F x) m = _ at h
  rw [parabolicHalfCharacter_eq_one_of_mem_standardCompact B F p hp, Units.val_one,
    one_mul, B.leviProjection_section] at h
  exact h

end Langlands.Global.AdelicBlockScalarSections
