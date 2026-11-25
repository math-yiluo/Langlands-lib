/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Detecting zero in a tensor product with a free module

If `N` is a free `R`-module, an element of `M ⊗[R] N` is zero once its images under `f i ⊗ N` are
zero for a jointly injective family of linear maps `f i : M → P i`: its coordinates in a basis of
`N` are elements of `M` killed by every `f i`.

## Main results

- `TensorProduct.eq_zero_of_forall_rTensor_eq_zero`
-/

@[expose] public section

open TensorProduct

/-- Let `N` be a free `R`-module and `f i : M →ₗ[R] P i` a jointly injective family of linear
maps. An element `t` of `M ⊗[R] N` with `(f i).rTensor N t = 0` for all `i` is zero.

Writing `t = ∑ⱼ mⱼ ⊗ bⱼ` in a basis `(bⱼ)` of `N`, the coordinates of `(f i).rTensor N t` are the
`f i mⱼ`, so every `mⱼ` is killed by all `f i`. -/
theorem TensorProduct.eq_zero_of_forall_rTensor_eq_zero {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module.Free R N] {ι : Type*}
    {P : ι → Type*} [∀ i, AddCommGroup (P i)] [∀ i, Module R (P i)] (f : ∀ i, M →ₗ[R] P i)
    (hf : ∀ m, (∀ i, f i m = 0) → m = 0) {t : M ⊗[R] N} (ht : ∀ i, (f i).rTensor N t = 0) :
    t = 0 := by
  classical
  let e := equivFinsuppOfBasisRight (M := M) (Module.Free.chooseBasis R N)
  let e' (i : ι) := equivFinsuppOfBasisRight (M := P i) (Module.Free.chooseBasis R N)
  have key (i : ι) (j) (t : M ⊗[R] N) : e' i ((f i).rTensor N t) j = f i (e t j) := by
    induction t using TensorProduct.inductionOn with
    | tmul m n => simp [e, e']
    | add x y hx hy => simp [hx, hy]
  apply e.injective
  ext j
  simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply]
  exact hf _ fun i ↦ by rw [← key, ht]; simp
