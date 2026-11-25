/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic

/-!
# Eigenvalues of tensor powers

Over a field, a pure tensor `⊗ᵢ vᵢ` of nonzero vectors is nonzero, so an eigenvalue `α` of `f`
gives the eigenvalue `αⁿ` of the `n`-th tensor power `f^{⊗n}`.

## Main results

- `PiTensorProduct.tprod_ne_zero`: a pure tensor of nonzero vectors is nonzero.
- `PiTensorProduct.hasEigenvalue_map_pow`: `αⁿ` is an eigenvalue of `f^{⊗n}`.
-/

@[expose] public section

open scoped TensorProduct

namespace PiTensorProduct

variable {K : Type*} [Field K] {ι : Type*} [Finite ι] {V : ι → Type*}
  [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]

/-- Over a field, a pure tensor of nonzero vectors is nonzero: choose linear forms `φᵢ` with
`φᵢ vᵢ ≠ 0`, then `⊗ᵢ φᵢ` does not vanish on `⊗ᵢ vᵢ`. -/
theorem tprod_ne_zero {v : ∀ i, V i} (hv : ∀ i, v i ≠ 0) : (⨂ₜ[K] i, v i) ≠ 0 := by
  have := Fintype.ofFinite ι
  have hφ (i : ι) : ∃ φ : Module.Dual K (V i), φ (v i) ≠ 0 := by
    by_contra! h
    exact hv i ((Module.forall_dual_apply_eq_zero_iff K (v i)).1 h)
  choose φ hφ using hφ
  intro h
  have := congrArg (lift ((MultilinearMap.mkPiAlgebra K ι K).compLinearMap φ)) h
  rw [lift.tprod, map_zero, MultilinearMap.compLinearMap_apply,
    MultilinearMap.mkPiAlgebra_apply] at this
  exact Finset.prod_ne_zero_iff.2 (fun i _ ↦ hφ i) this

/-- If `α` is an eigenvalue of `f`, then `αⁿ` is an eigenvalue of the tensor power
`f^{⊗n} = ⨂_{i < n} f`. (blueprint: `lemma-filtrations-spectra`) -/
theorem hasEigenvalue_map_pow {W : Type*} [AddCommGroup W] [Module K W] {f : Module.End K W}
    {α : K} (hα : f.HasEigenvalue α) (n : ℕ) :
    Module.End.HasEigenvalue (map fun _ : Fin n ↦ f) (α ^ n) := by
  obtain ⟨v, hv⟩ := hα.exists_hasEigenvector
  refine Module.End.hasEigenvalue_of_hasEigenvector (x := ⨂ₜ[K] _ : Fin n, v) ⟨?_, ?_⟩
  · rw [Module.End.mem_eigenspace_iff, map_tprod]
    simp only [hv.apply_eq_smul]
    rw [MultilinearMap.map_smul_univ, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  · exact tprod_ne_zero fun _ ↦ hv.2

end PiTensorProduct
