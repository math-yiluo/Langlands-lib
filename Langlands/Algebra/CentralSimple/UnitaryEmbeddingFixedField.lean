import Langlands.GroupScheme.Quaternionic.Involution
import Langlands.GroupScheme.Examples.SU3RootParametersQuadratic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.Flat.Basic

/-! # Tensor coordinates from the fixed field of a quadratic involution -/

noncomputable section

open scoped TensorProduct

namespace Langlands.CentralSimple

open Langlands.GroupScheme.Quaternionic Langlands.GroupScheme.SU3Root

universe u

variable {F P : Type u} [Field F] [Field P] [Algebra F P]
  (σ : FirstKindInvolution F P)

private def fieldAut : P ≃ₐ[F] P where
  toFun := σ
  invFun := σ
  left_inv := σ.apply_apply
  right_inv := σ.apply_apply
  map_mul' x y := (σ.map_mul x y).trans (mul_comm _ _)
  map_add' := σ.map_add
  commutes' := σ.map_algebraMap

/-- The intermediate field of elements fixed by the involution. -/
def unitaryEmbeddingFixedField : IntermediateField F P :=
  IntermediateField.fixedField (Subgroup.zpowers (fieldAut σ))

theorem mem_unitaryEmbeddingFixedField (x : P) :
    x ∈ unitaryEmbeddingFixedField σ ↔ σ x = x := by
  rw [unitaryEmbeddingFixedField, IntermediateField.mem_fixedField_iff]
  constructor
  · intro h
    exact h (fieldAut σ) (Subgroup.mem_zpowers (fieldAut σ))
  · intro h f hf
    exact smul_eq_self_of_mem_zpowers hf h

/-- The fixed field of a nontrivial field involution has index two. -/
theorem unitaryEmbeddingFixedField_finrank [FiniteDimensional F P]
    (hσ : ∃ p : P, σ p ≠ p) : Module.finrank (unitaryEmbeddingFixedField σ) P = 2 := by
  obtain ⟨p, hp⟩ := hσ
  have hne : fieldAut σ ≠ 1 := fun h => hp (DFunLike.congr_fun h p)
  have hsq : fieldAut σ ^ 2 = 1 := by
    ext x
    exact σ.apply_apply x
  rw [unitaryEmbeddingFixedField, IntermediateField.finrank_fixedField_eq_card,
    Nat.card_zpowers, orderOf_eq_prime hsq hne]

private theorem exists_not_fixed {E : Type u} [Field E] [Algebra F E] [Algebra E P]
    [IsScalarTower F E P] [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E]
    (hσ : ∀ e : E, σ (algebraMap E P e) = algebraMap E P (conjugation F E e)) :
    ∃ e : E, σ (algebraMap E P e) ≠ algebraMap E P e := by
  by_contra! h
  apply conjugation_ne_one F E
  ext e
  exact (algebraMap E P).injective ((hσ e).symm.trans (h e))

section Compositum

variable {E : Type u} [Field E] [Algebra F E] [Algebra E P] [IsScalarTower F E P]
  [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E]
  [FiniteDimensional E P] [CharZero F]

/-- If the involution extends quadratic conjugation on `E`, the multiplication
map identifies `P` with `E` tensored over `F` with the fixed field. -/
def unitaryEmbeddingFixedFieldTensorEquiv
    (hσ : ∀ e : E, σ (algebraMap E P e) = algebraMap E P (conjugation F E e)) :
    E ⊗[F] unitaryEmbeddingFixedField σ ≃ₐ[E] P := by
  let K := unitaryEmbeddingFixedField σ
  letI : FiniteDimensional F E := .of_finrank_pos (by
    rw [Algebra.IsQuadraticExtension.finrank_eq_two F E]
    decide)
  letI : FiniteDimensional F P := Module.Finite.trans E P
  letI : CharZero P := charZero_of_injective_algebraMap (algebraMap F P).injective
  have hP : Module.finrank K P = 2 := by
    obtain ⟨e, he⟩ := exists_not_fixed σ hσ
    exact unitaryEmbeddingFixedField_finrank σ ⟨algebraMap E P e, he⟩
  have hdim : Module.finrank E (E ⊗[F] K) = Module.finrank E P := by
    rw [Module.finrank_baseChange]
    have hK := Module.finrank_mul_finrank F K P
    have hE := Module.finrank_mul_finrank F E P
    rw [hP] at hK
    rw [Algebra.IsQuadraticExtension.finrank_eq_two F E] at hE
    omega
  let f : E ⊗[F] K →ₐ[E] P := Algebra.TensorProduct.lift (Algebra.ofId E P) K.val
    (fun _ _ => Commute.all _ _)
  have hs : Function.Surjective f := by
    obtain ⟨e, he⟩ := exists_not_fixed σ hσ
    let ω := e - conjugation F E e
    let t := algebraMap E P ω
    have ht : t ≠ 0 := by
      change algebraMap E P (e - conjugation F E e) ≠ 0
      rw [map_sub, sub_ne_zero]
      rwa [hσ, ne_comm] at he
    have hneg : σ t = -t := by
      change σ (algebraMap E P (e - conjugation F E e)) =
        -algebraMap E P (e - conjugation F E e)
      rw [hσ, map_sub, conjugation_involutive F E e, map_sub, map_sub, neg_sub]
    intro x
    have htwo : (2 : P) ≠ 0 := two_ne_zero
    let x₀ : K := ⟨(x + σ x) / 2, (mem_unitaryEmbeddingFixedField σ _).mpr (by
      change fieldAut σ ((x + σ x) / 2) = (x + σ x) / 2
      rw [map_div₀, map_add, map_ofNat]
      change (σ x + σ (σ x)) / 2 = _
      rw [σ.apply_apply, add_comm (σ x)])⟩
    let x₁ : K := ⟨(x - σ x) / (2 * t), (mem_unitaryEmbeddingFixedField σ _).mpr (by
      change fieldAut σ ((x - σ x) / (2 * t)) = (x - σ x) / (2 * t)
      rw [map_div₀, map_sub, map_mul, map_ofNat]
      change (σ x - σ (σ x)) / (2 * σ t) = _
      rw [σ.apply_apply, hneg, mul_neg, div_neg, ← neg_sub, neg_div, neg_neg])⟩
    refine ⟨(1 : E) ⊗ₜ[F] x₀ + ω ⊗ₜ[F] x₁, ?_⟩
    rw [map_add, Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.lift_tmul]
    change algebraMap E P 1 * ((x + σ x) / 2) + t * ((x - σ x) / (2 * t)) = x
    rw [map_one, one_mul]
    field_simp
    ring
  exact AlgEquiv.ofBijective f
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hs, hs⟩

@[simp] theorem unitaryEmbeddingFixedFieldTensorEquiv_tmul
    (hσ : ∀ e : E, σ (algebraMap E P e) = algebraMap E P (conjugation F E e))
    (e : E) (x : unitaryEmbeddingFixedField σ) :
    unitaryEmbeddingFixedFieldTensorEquiv σ hσ (e ⊗ₜ[F] x) = algebraMap E P e * (x : P) :=
  rfl

end Compositum

section Coefficients

variable (R : Type u) [CommRing R] [Algebra F R]

/-- The inclusion of the fixed field extended to the coefficient algebra. -/
def unitaryEmbeddingFixedInclusion : R ⊗[F] unitaryEmbeddingFixedField σ →ₐ[R] R ⊗[F] P :=
  Algebra.TensorProduct.map (AlgHom.id R R) (unitaryEmbeddingFixedField σ).val

theorem unitaryEmbeddingFixedInclusion_injective :
    Function.Injective (unitaryEmbeddingFixedInclusion σ R) :=
  Module.Flat.lTensor_preserves_injective_linearMap
    (unitaryEmbeddingFixedField σ).val.toLinearMap Subtype.val_injective

@[simp] theorem unitaryEmbeddingFixedInclusion_tmul
    (r : R) (x : unitaryEmbeddingFixedField σ) :
    unitaryEmbeddingFixedInclusion σ R (r ⊗ₜ[F] x) = r ⊗ₜ[F] (x : P) := rfl

/-- After scalar extension the fixed elements are the image of the scalar-extended
fixed field. -/
theorem unitaryEmbeddingFixedInclusion_range [CharZero F] (x : R ⊗[F] P) :
    (∃ y, unitaryEmbeddingFixedInclusion σ R y = x) ↔ σ.baseChange R x = x := by
  constructor
  · rintro ⟨y, rfl⟩
    induction y using TensorProduct.inductionOn with
    | tmul r y => simp [(mem_unitaryEmbeddingFixedField σ _).mp y.2]
    | add y z hy hz => simp [hy, hz]
  · intro hx
    let l : P →ₗ[F] unitaryEmbeddingFixedField σ :=
      { toFun := fun p => ⟨(2 : F)⁻¹ • (p + σ p),
          (mem_unitaryEmbeddingFixedField σ _).mpr (by simp [add_comm])⟩
        map_add' := fun p q => Subtype.ext (by
          simp [smul_add]
          ac_rfl)
        map_smul' := fun c p => Subtype.ext (by simp [smul_add, smul_smul, mul_comm]) }
    have h (t : R ⊗[F] P) : unitaryEmbeddingFixedInclusion σ R (l.baseChange R t) =
        (2 : F)⁻¹ • (t + σ.baseChange R t) := by
      induction t using TensorProduct.inductionOn with
      | tmul r p =>
        rw [LinearMap.baseChange_tmul, unitaryEmbeddingFixedInclusion_tmul,
          FirstKindInvolution.baseChange_tmul, ← TensorProduct.tmul_add, ← TensorProduct.tmul_smul]
        rfl
      | add t s ht hs =>
        simp only [map_add, ht, hs, smul_add]
        ac_rfl
    refine ⟨l.baseChange R x, ?_⟩
    rw [h, hx, ← two_smul F, inv_smul_smul₀ two_ne_zero]

/-- A fixed unit descends to a unit of the scalar extension of the fixed field. -/
theorem exists_unitaryEmbeddingFixedInclusion_unit [CharZero F] (x : (R ⊗[F] P)ˣ)
    (hx : σ.baseChange R (x : R ⊗[F] P) = x) :
    ∃ y : (R ⊗[F] unitaryEmbeddingFixedField σ)ˣ,
      Units.map (unitaryEmbeddingFixedInclusion σ R).toMonoidHom y = x := by
  have hi : σ.baseChange R (↑x⁻¹ : R ⊗[F] P) = (↑x⁻¹ : R ⊗[F] P) := by
    have h := congrArg (σ.baseChange R) (Units.mul_inv x)
    rw [FirstKindInvolution.map_mul, hx, FirstKindInvolution.map_one] at h
    simpa using congrArg (fun y : R ⊗[F] P => y * (↑x⁻¹ : R ⊗[F] P)) h
  obtain ⟨y, hy⟩ := (unitaryEmbeddingFixedInclusion_range σ R x).mpr hx
  obtain ⟨z, hz⟩ := (unitaryEmbeddingFixedInclusion_range σ R (↑x⁻¹)).mpr hi
  have hmul : y * z = 1 := (unitaryEmbeddingFixedInclusion_injective σ R) (by
    calc
      _ = (x : R ⊗[F] P) * (↑x⁻¹ : R ⊗[F] P) := by rw [map_mul, hy, hz]
      _ = 1 := Units.mul_inv x
      _ = _ := (unitaryEmbeddingFixedInclusion σ R).map_one.symm)
  exact ⟨⟨y, z, hmul, (mul_comm z y).trans hmul⟩, Units.ext hy⟩

end Coefficients

end Langlands.CentralSimple
