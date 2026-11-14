import Langlands.GroupScheme.IntegralModel.Smoothening.TensorDensity
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-! # Tensor density for the locus of elements with values in the maximal ideal

Over a local ring `R`, let `F` be a family of `R`-valued forms on `C` and `G` one on `D`. Let
`maxLocus F` be the submodule of elements of `C` all of whose values lie in the maximal ideal.
An element of `C ⊗ D` all of whose values under the product forms lie in the maximal ideal lies
in `C ⊗ maxLocus G + maxLocus F ⊗ D`. This generalizes `DetectsMaximal.tensor`, which is the case
`maxLocus F = 𝔪 C`. -/

noncomputable section

universe u

open IsLocalRing TensorProduct LinearMap

namespace Langlands.GroupScheme.IntegralModel.Smoothening.Termination

variable {R : Type u} [CommRing R] [IsLocalRing R]

section BaseForm

variable {M : Type*} [AddCommGroup M] [Module R M]

/-- The base change to the residue field of a residue-field-valued form. -/
def baseForm (g : M →ₗ[R] ResidueField R) :
    ResidueField R ⊗[R] M →ₗ[ResidueField R] ResidueField R :=
  TensorProduct.AlgebraTensorModule.lift
    (LinearMap.toSpanSingleton (ResidueField R) (M →ₗ[R] ResidueField R) g)

@[simp]
theorem baseForm_tmul (g : M →ₗ[R] ResidueField R) (a : ResidueField R) (m : M) :
    baseForm g (a ⊗ₜ m) = a * g m := by
  simp [baseForm]

/-- The product of two residue-field-valued forms. -/
def pform {N : Type*} [AddCommGroup N] [Module R N] (g : M →ₗ[R] ResidueField R)
    (h : N →ₗ[R] ResidueField R) : M ⊗[R] N →ₗ[R] ResidueField R :=
  (Algebra.TensorProduct.lmul' R (S := ResidueField R)).toLinearMap ∘ₗ TensorProduct.map g h

@[simp]
theorem pform_tmul {N : Type*} [AddCommGroup N] [Module R N] (g : M →ₗ[R] ResidueField R)
    (h : N →ₗ[R] ResidueField R) (m : M) (n : N) : pform g h (m ⊗ₜ n) = g m * h n := by
  simp [pform]

theorem baseForm_product {N : Type*} [AddCommGroup N] [Module R N]
    (g : M →ₗ[R] ResidueField R) (h : N →ₗ[R] ResidueField R) (y : M ⊗[R] N) :
    TensorProduct.lid _ _ (TensorProduct.map (baseForm g) (baseForm h)
        (TensorProduct.AlgebraTensorModule.distribBaseChange R (ResidueField R) M N
          ((1 : ResidueField R) ⊗ₜ y))) = pform g h y := by
  induction y using TensorProduct.inductionOn with
  | tmul m n =>
    rw [TensorProduct.AlgebraTensorModule.distribBaseChange_tmul]
    simp
  | add x y hx hy =>
    rw [TensorProduct.tmul_add, map_add, map_add, map_add, hx, hy, map_add]

/-- A module killed by the maximal ideal on which the forms detect zero. -/
theorem detects_baseForm {ι : Type*} (g : ι → M →ₗ[R] ResidueField R)
    (hg : ∀ m : M, (∀ i, g i m = 0) → m = 0) :
    Detects (fun i => baseForm (g i)) := by
  intro v hv
  obtain ⟨m, rfl⟩ := exists_one_tmul_eq v
  have : m = 0 := hg m fun i => by
    have := hv i
    simpa using this
  rw [this, TensorProduct.tmul_zero]

theorem smul_top_eq_bot_of_killed {N : Type*} [AddCommGroup N] [Module R N]
    (hM : ∀ r ∈ maximalIdeal R, ∀ m : M, r • m = 0) :
    (maximalIdeal R • (⊤ : Submodule R (M ⊗[R] N))) = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  refine Submodule.smul_induction_on hy ?_ ?_
  · intro r hr t ht
    clear ht
    rw [Submodule.mem_bot]
    induction t using TensorProduct.inductionOn with
    | tmul m n => rw [TensorProduct.smul_tmul', hM r hr m, TensorProduct.zero_tmul]
    | add x y hx hy => rw [smul_add, hx, hy, add_zero]
  · intro a b ha hb
    rw [Submodule.mem_bot] at ha hb ⊢
    rw [ha, hb, add_zero]

/-- Product forms detect zero on a tensor product of modules killed by the maximal ideal. -/
theorem eq_zero_of_pform {N : Type*} [AddCommGroup N] [Module R N] {ι κ : Type*}
    (g : ι → M →ₗ[R] ResidueField R) (h : κ → N →ₗ[R] ResidueField R)
    (hM : ∀ r ∈ maximalIdeal R, ∀ m : M, r • m = 0)
    (hg : ∀ m : M, (∀ i, g i m = 0) → m = 0) (hh : ∀ n : N, (∀ j, h j n = 0) → n = 0)
    (y : M ⊗[R] N) (hy : ∀ i j, pform (g i) (h j) y = 0) : y = 0 := by
  have h1 : (1 : ResidueField R) ⊗ₜ[R] y = 0 := by
    apply (TensorProduct.AlgebraTensorModule.distribBaseChange R (ResidueField R) M N).injective
    rw [map_zero]
    refine detects_tensor (detects_baseForm g hg) (detects_baseForm h hh) _ fun i j => ?_
    rw [baseForm_product]
    exact hy i j
  rw [one_tmul_eq_zero_iff, smul_top_eq_bot_of_killed hM] at h1
  exact h1

end BaseForm

section MaxLocus

variable {C : Type*} [AddCommGroup C] [Module R C]

/-- The elements all of whose values lie in the maximal ideal. -/
def maxLocus {ι : Type*} (F : ι → C →ₗ[R] R) : Submodule R C where
  carrier := {c | ∀ i, F i c ∈ maximalIdeal R}
  add_mem' ha hb i := by rw [map_add]; exact Ideal.add_mem _ (ha i) (hb i)
  zero_mem' i := by rw [map_zero]; exact Ideal.zero_mem _
  smul_mem' r c hc i := by rw [map_smul, smul_eq_mul]; exact Ideal.mul_mem_left _ r (hc i)

theorem mem_maxLocus {ι : Type*} {F : ι → C →ₗ[R] R} {c : C} :
    c ∈ maxLocus F ↔ ∀ i, F i c ∈ maximalIdeal R := Iff.rfl

/-- The residue of a form on the quotient by the locus. -/
def quotForm {ι : Type*} (F : ι → C →ₗ[R] R) (i : ι) :
    (C ⧸ maxLocus F) →ₗ[R] ResidueField R :=
  (maxLocus F).liftQ ((Algebra.linearMap R (ResidueField R)) ∘ₗ F i) (by
    intro c hc
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Algebra.linearMap_apply,
      IsLocalRing.ResidueField.algebraMap_eq, residue_eq_zero_iff]
    exact hc i)

@[simp]
theorem quotForm_mk {ι : Type*} (F : ι → C →ₗ[R] R) (i : ι) (c : C) :
    quotForm F i (Submodule.Quotient.mk c) = residue R (F i c) := rfl

theorem quot_killed {ι : Type*} (F : ι → C →ₗ[R] R) :
    ∀ r ∈ maximalIdeal R, ∀ m : C ⧸ maxLocus F, r • m = 0 := by
  intro r hr m
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  intro i
  rw [map_smul, smul_eq_mul]
  exact Ideal.mul_mem_right _ _ hr

theorem quot_detects {ι : Type*} (F : ι → C →ₗ[R] R) :
    ∀ m : C ⧸ maxLocus F, (∀ i, quotForm F i m = 0) → m = 0 := by
  intro m hm
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  rw [Submodule.Quotient.mk_eq_zero]
  intro i
  have := hm i
  rw [quotForm_mk, residue_eq_zero_iff] at this
  exact this

variable {D : Type*} [AddCommGroup D] [Module R D]

/-- **Tensor density for the maximal locus.** -/
theorem mem_sup_of_productForm {ι κ : Type*} (F : ι → C →ₗ[R] R) (G : κ → D →ₗ[R] R)
    (x : C ⊗[R] D) (hx : ∀ i j, productForm (F i) (G j) x ∈ maximalIdeal R) :
    x ∈ range (lTensor C (maxLocus G).subtype) ⊔ range (rTensor D (maxLocus F).subtype) := by
  rw [← TensorProduct.map_ker (LinearMap.exact_subtype_mkQ _) (Submodule.mkQ_surjective _)
    (LinearMap.exact_subtype_mkQ _) (Submodule.mkQ_surjective _), LinearMap.mem_ker]
  refine eq_zero_of_pform (quotForm F) (quotForm G) (quot_killed F) (quot_detects F)
    (quot_detects G) _ fun i j => ?_
  have key : ∀ y : C ⊗[R] D, pform (quotForm F i) (quotForm G j)
      (TensorProduct.map (maxLocus F).mkQ (maxLocus G).mkQ y) =
      residue R (productForm (F i) (G j) y) := by
    intro y
    induction y using TensorProduct.inductionOn with
    | tmul c d => simp
    | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]
  rw [key, residue_eq_zero_iff]
  exact hx i j

end MaxLocus

end Langlands.GroupScheme.IntegralModel.Smoothening.Termination
