import Langlands.Representation.Tensor.UnitaryStatement
import Langlands.Representation.Tensor.FiniteEquivalences
import Mathlib.Analysis.InnerProductSpace.TensorProduct

/-!
# Invariant positive forms on finite external tensor products: proof

Positive definite cores are built on `Fin n`-indexed tensors by splitting off the
first factor and using Mathlib's binary algebraic tensor inner product, then
transported to an arbitrary finite index type. Invariance is checked on pure
tensors and extended by sesquilinearity.
-/

noncomputable section

open scoped TensorProduct

namespace Langlands.FiniteTensor

universe uI uG uV uE uF

namespace InvariantPositiveFormProof

section Core

variable {E : Type uE} [AddCommGroup E] [Module ℂ E]
variable {F : Type uF} [AddCommGroup F] [Module ℂ F]

/-- Pull back a positive definite core along an injective linear map. -/
@[instance_reducible]
def coreComap (c : InnerProductSpace.Core ℂ F) (f : E →ₗ[ℂ] F)
    (hf : Function.Injective f) : InnerProductSpace.Core ℂ E where
  inner x y := c.inner (f x) (f y)
  conj_inner_symm x y := c.conj_inner_symm (f x) (f y)
  re_inner_nonneg x := c.re_inner_nonneg (f x)
  add_left x y z := by
    change c.inner (f (x + y)) (f z) = c.inner (f x) (f z) + c.inner (f y) (f z)
    rw [map_add, c.add_left]
  smul_left x y r := by
    change c.inner (f (r • x)) (f y) = _
    rw [map_smul, c.smul_left]
  definite x hx := hf (by rw [map_zero]; exact c.definite (f x) hx)

theorem coreComap_inner (c : InnerProductSpace.Core ℂ F) (f : E →ₗ[ℂ] F)
    (hf : Function.Injective f) (x y : E) :
    (coreComap c f hf).inner x y = c.inner (f x) (f y) := rfl

theorem core_inner_add_right (c : InnerProductSpace.Core ℂ E) (x y z : E) :
    c.inner x (y + z) = c.inner x y + c.inner x z := by
  rw [← c.conj_inner_symm x (y + z), c.add_left, map_add, c.conj_inner_symm,
    c.conj_inner_symm]

theorem core_inner_smul_right (c : InnerProductSpace.Core ℂ E) (x y : E) (r : ℂ) :
    c.inner x (r • y) = r * c.inner x y := by
  rw [← c.conj_inner_symm x (r • y), c.smul_left, map_mul, c.conj_inner_symm,
    Complex.conj_conj]

/-- The binary algebraic tensor product of two positive definite cores, using the
normed structures induced by the supplied cores. -/
theorem exists_core_tmul (cE : InnerProductSpace.Core ℂ E)
    (cF : InnerProductSpace.Core ℂ F) :
    ∃ C : InnerProductSpace.Core ℂ (E ⊗[ℂ] F), ∀ (x x' : E) (y y' : F),
      C.inner (x ⊗ₜ[ℂ] y) (x' ⊗ₜ[ℂ] y') = cE.inner x x' * cF.inner y y' := by
  let := cE
  let : NormedAddCommGroup E := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  let : InnerProductSpace ℂ E := InnerProductSpace.ofCore
    (inferInstance : PreInnerProductSpace.Core ℂ E)
  let := cF
  let : NormedAddCommGroup F := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  let : InnerProductSpace ℂ F := InnerProductSpace.ofCore
    (inferInstance : PreInnerProductSpace.Core ℂ F)
  exact ⟨InnerProductSpace.toCore, fun x x' y y' => TensorProduct.inner_tmul ℂ x x' y y'⟩

end Core

/-- Positive definite product cores on `Fin n`-indexed tensors. -/
theorem exists_core_fin : ∀ (n : ℕ) (V : Fin n → Type uV) [∀ i, AddCommGroup (V i)]
    [∀ i, Module ℂ (V i)] (c : ∀ i, InnerProductSpace.Core ℂ (V i)),
    ∃ C : InnerProductSpace.Core ℂ (PiTensorProduct ℂ V), ∀ v w : ∀ i, V i,
      C.inner (PiTensorProduct.tprod ℂ v) (PiTensorProduct.tprod ℂ w) =
        ∏ i, (c i).inner (v i) (w i)
  | 0, V, _, _, c => by
    refine ⟨coreComap InnerProductSpace.toCore
      (PiTensorProduct.isEmptyEquiv (R := ℂ) (s := V) (Fin 0)).toLinearMap
      (LinearEquiv.injective _), ?_⟩
    intro v w
    rw [coreComap_inner]
    simp only [LinearEquiv.coe_coe, PiTensorProduct.isEmptyEquiv_apply_tprod,
      Finset.univ_eq_empty, Finset.prod_empty]
    change inner ℂ (1 : ℂ) 1 = 1
    simp
  | n + 1, V, _, _, c => by
    obtain ⟨C₁, hC₁⟩ := exists_core_fin n (fun j => V j.succ) (fun j => c j.succ)
    obtain ⟨C₂, hC₂⟩ := exists_core_tmul (c 0) C₁
    refine ⟨coreComap C₂ (headTailLinearEquiv ℂ V).toLinearMap
      (LinearEquiv.injective _), ?_⟩
    intro v w
    rw [coreComap_inner, LinearEquiv.coe_coe, headTailLinearEquiv_tprod,
      headTailLinearEquiv_tprod, hC₂, hC₁, Fin.prod_univ_succ]

/-- Positive definite product cores on tensors over an arbitrary finite index type. -/
theorem exists_core (ι : Type uI) [Fintype ι] (V : ι → Type uV)
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (c : ∀ i, InnerProductSpace.Core ℂ (V i)) :
    ∃ C : InnerProductSpace.Core ℂ (PiTensorProduct ℂ V), ∀ v w : ∀ i, V i,
      C.inner (PiTensorProduct.tprod ℂ v) (PiTensorProduct.tprod ℂ w) =
        ∏ i, (c i).inner (v i) (w i) := by
  classical
  let e := Fintype.equivFin ι
  obtain ⟨C, hC⟩ := exists_core_fin (Fintype.card ι) (fun k => V (e.symm k))
    (fun k => c (e.symm k))
  refine ⟨coreComap C (PiTensorProduct.reindex ℂ V e).toLinearMap
    (LinearEquiv.injective _), ?_⟩
  intro v w
  rw [coreComap_inner, LinearEquiv.coe_coe, PiTensorProduct.reindex_tprod,
    PiTensorProduct.reindex_tprod, hC]
  exact e.symm.prod_comp (fun i => (c i).inner (v i) (w i))

/-- A linear operator preserving a core on pure tensors preserves it everywhere. -/
theorem core_inner_map_map {ι : Type uI} {V : ι → Type uV}
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (C : InnerProductSpace.Core ℂ (PiTensorProduct ℂ V))
    (T : PiTensorProduct ℂ V →ₗ[ℂ] PiTensorProduct ℂ V)
    (hT : ∀ v w : ∀ i, V i,
      C.inner (T (PiTensorProduct.tprod ℂ v)) (T (PiTensorProduct.tprod ℂ w)) =
        C.inner (PiTensorProduct.tprod ℂ v) (PiTensorProduct.tprod ℂ w))
    (x y : PiTensorProduct ℂ V) : C.inner (T x) (T y) = C.inner x y := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r v =>
    induction y using PiTensorProduct.induction_on with
    | smul_tprod s w =>
      rw [map_smul, map_smul, C.smul_left, C.smul_left, core_inner_smul_right,
        core_inner_smul_right, hT]
    | add y₁ y₂ h₁ h₂ =>
      rw [map_add, core_inner_add_right, core_inner_add_right, h₁, h₂]
  | add x₁ x₂ h₁ h₂ =>
    rw [map_add, C.add_left, C.add_left, h₁, h₂]

end InvariantPositiveFormProof

open InvariantPositiveFormProof in
/-- The actual external tensor product of invariant positive forms carries an
invariant positive form given by the product formula on pure tensors. -/
theorem invariantPositiveForm : InvariantPositiveFormStatement.{uI, uG, uV} := by
  intro ι _ G _ V _ _ ρ b
  obtain ⟨C, hC⟩ := exists_core ι V (fun i => (b i).toInnerProductCore)
  refine ⟨{ toInnerProductCore := C, invariant := fun g x y => ?_ }, hC⟩
  refine core_inner_map_map C (external ρ g) (fun v w => ?_) x y
  rw [external_tprod, external_tprod, hC, hC]
  exact Finset.prod_congr rfl (fun i _ => (b i).invariant (g i) (v i) (w i))

end Langlands.FiniteTensor
