import Mathlib.LinearAlgebra.TensorProduct.Basis
import Langlands.Representation.Tensor.SmoothDualInjectivityProof

/-! # Product functionals and partial contractions of finite tensors -/

noncomputable section

open scoped BigOperators TensorProduct

set_option autoImplicit false

namespace Langlands.FiniteTensor

section Indexed

variable {𝕜 ι : Type*} [Field 𝕜] [Fintype ι]
  {V : ι → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module 𝕜 (V i)]

/-- The functional sending an elementary tensor to the product of the factor values. -/
def productFunctional (ℓ : ∀ i, Module.Dual 𝕜 (V i)) : Module.Dual 𝕜 (⨂[𝕜] i, V i) :=
  PiTensorProduct.dualDistrib (PiTensorProduct.tprod 𝕜 ℓ)

@[simp]
theorem productFunctional_tprod (ℓ : ∀ i, Module.Dual 𝕜 (V i)) (v : ∀ i, V i) :
    productFunctional ℓ (PiTensorProduct.tprod 𝕜 v) = ∏ i, ℓ i (v i) :=
  PiTensorProduct.dualDistrib_apply ℓ v

variable {W : ι → Type*} [∀ i, AddCommGroup (W i)] [∀ i, Module 𝕜 (W i)]

/-- Pullback of a product functional along factor maps. -/
theorem productFunctional_map (ℓ : ∀ i, Module.Dual 𝕜 (W i)) (A : ∀ i, V i →ₗ[𝕜] W i)
    (z : ⨂[𝕜] i, V i) :
    productFunctional ℓ (PiTensorProduct.map A z) =
      productFunctional (fun i => (ℓ i).comp (A i)) z := by
  induction z using PiTensorProduct.induction_on with
  | smul_tprod c v => simp [PiTensorProduct.map_tprod]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Fix all but one of the factors of a product functional. For any tensor the resulting
linear test on endomorphisms of the chosen factor is evaluation on a single vector. -/
theorem exists_productFunctional_slice [DecidableEq ι] (ℓ : ∀ i, Module.Dual 𝕜 (V i))
    (i : ι) (z : ⨂[𝕜] i, V i) :
    ∃ v : V i, ∀ A : Module.End 𝕜 (V i),
      productFunctional ℓ (PiTensorProduct.map (Function.update (fun _ => LinearMap.id) i A) z) =
        ℓ i (A v) := by
  induction z using PiTensorProduct.induction_on with
  | smul_tprod c v =>
    refine ⟨(c * ∏ j ∈ Finset.univ.erase i, ℓ j (v j)) • v i, fun A => ?_⟩
    simp only [map_smul, PiTensorProduct.map_tprod, productFunctional_tprod, smul_eq_mul]
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i), Function.update_self]
    have h : (∏ j ∈ Finset.univ.erase i,
        ℓ j (Function.update (fun _ => LinearMap.id) i A j (v j))) =
        ∏ j ∈ Finset.univ.erase i, ℓ j (v j) := by
      refine Finset.prod_congr rfl fun j hj => ?_
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hj), LinearMap.id_apply]
    rw [h, mul_assoc]
  | add x y hx hy =>
    obtain ⟨v, hv⟩ := hx
    obtain ⟨w, hw⟩ := hy
    exact ⟨v + w, fun A => by simp only [map_add, hv A, hw A]⟩

private def freeEvaluation {P : Type*} {U : Type*} [AddCommGroup U] [Module 𝕜 U]
    (ℓ : P → Module.Dual 𝕜 U) : U →ₗ[𝕜] Module.Dual 𝕜 (P →₀ 𝕜) :=
  (Finsupp.linearCombination 𝕜 ℓ).flip

private theorem freeEvaluation_single {P : Type*} {U : Type*} [AddCommGroup U] [Module 𝕜 U]
    (ℓ : P → Module.Dual 𝕜 U) (x : U) (p : P) :
    freeEvaluation ℓ x (Finsupp.single p 1) = ℓ p x := by
  simp [freeEvaluation]

/-- A family of separating functionals on each factor gives separating product
functionals on the finite tensor product. -/
theorem productFunctional_separates {P : ι → Type*} (ℓ : ∀ i, P i → Module.Dual 𝕜 (V i))
    (hℓ : ∀ i (x : V i), (∀ p, ℓ i p x = 0) → x = 0)
    (z : ⨂[𝕜] i, V i) (hz : ∀ p : ∀ i, P i, productFunctional (fun i => ℓ i (p i)) z = 0) :
    z = 0 := by
  let eval := fun i => freeEvaluation (ℓ i)
  have hinj (i : ι) : Function.Injective (eval i) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    apply hℓ i x
    intro p
    simpa only [eval, freeEvaluation_single, LinearMap.zero_apply] using
      LinearMap.congr_fun hx (Finsupp.single p 1)
  let pair := PiTensorProduct.dualDistrib ∘ₗ PiTensorProduct.map eval
  have hpair (p : ∀ i, P i) :
      pair.flip (PiTensorProduct.tprod 𝕜 (fun i => Finsupp.single (p i) 1)) =
        productFunctional (fun i => ℓ i (p i)) := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.flip_apply, pair, LinearMap.comp_apply,
      PiTensorProduct.map_tprod, PiTensorProduct.dualDistrib_apply, eval, freeEvaluation_single,
      productFunctional_tprod]
  apply (dualDistrib_comp_map_injective eval hinj : Function.Injective pair)
  rw [map_zero]
  apply (Basis.piTensorProduct (fun _ => Finsupp.basisSingleOne)).ext
  intro p
  simpa only [Basis.piTensorProduct_apply, Finsupp.coe_basisSingleOne, LinearMap.zero_apply,
    LinearMap.flip_apply] using LinearMap.congr_fun (hpair p) z |>.trans (hz p)

end Indexed

section Binary

variable {𝕜 V M : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V] [AddCommGroup M] [Module 𝕜 M]

/-- Contract the second factor of a tensor against an algebraic linear functional. -/
def contractRight (μ : Module.Dual 𝕜 M) : V ⊗[𝕜] M →ₗ[𝕜] V :=
  (TensorProduct.rid 𝕜 V).toLinearMap.comp (TensorProduct.map LinearMap.id μ)

@[simp]
theorem contractRight_tmul (μ : Module.Dual 𝕜 M) (v : V) (m : M) :
    contractRight μ (v ⊗ₜ[𝕜] m) = μ m • v := by
  simp [contractRight]

/-- Endomorphisms of the first factor commute with contraction of the second. -/
theorem contractRight_map (μ : Module.Dual 𝕜 M) (A : Module.End 𝕜 V) (z : V ⊗[𝕜] M) :
    contractRight μ (TensorProduct.map A LinearMap.id z) = A (contractRight μ z) := by
  induction z using TensorProduct.inductionOn with
  | tmul v m => simp
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The contractions against the full algebraic dual of the second factor separate tensors. -/
theorem eq_zero_of_contractRight (z : V ⊗[𝕜] M)
    (hz : ∀ μ : Module.Dual 𝕜 M, contractRight μ z = 0) : z = 0 := by
  let b := Module.Free.chooseBasis 𝕜 M
  let e := TensorProduct.equivFinsuppOfBasisRight (M := V) b
  have he (x : V ⊗[𝕜] M) (j : Module.Free.ChooseBasisIndex 𝕜 M) :
      e x j = contractRight (b.coord j) x := by
    induction x using TensorProduct.inductionOn with
    | tmul v m => simp [e, Module.Basis.coord_apply]
    | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  apply e.injective
  ext j
  simp only [map_zero, Finsupp.zero_apply, he, hz]

end Binary

end Langlands.FiniteTensor
