# Termination of the smoothening sequence: tensor density for the maximal locus

Author: Worker 348. Internal helper module for Kaletha–Prasad, Theorem A.6.2. The route is internal
to this project: it is used to show that the comultiplication of `B = integralFunctions R K A`
maps each member of the smoothening sequence into the span of its tensor square
(`TerminationChain`).

Namespace: `Langlands.GroupScheme.IntegralModel.Smoothening.Termination`. Throughout, `R` is a local
ring with maximal ideal `𝔪` and residue field `k`.

## Forms with values in the residue field

For an `R`-module `M`:

- `baseForm g : k ⊗[R] M →ₗ[k] k` is the base change of a form `g : M →ₗ[R] k`. It satisfies
  `baseForm g (a ⊗ m) = a * g m` (`baseForm_tmul`).
- `pform g h : M ⊗[R] N →ₗ[R] k` is the product form `m ⊗ n ↦ g m * h n` (`pform_tmul`).
- `baseForm_product`: under `k ⊗ (M ⊗ N) ≅ (k ⊗ M) ⊗_k (k ⊗ N)`, the tensor product of the base
  changed forms evaluated at `1 ⊗ y` equals `pform g h y`.
- `detects_baseForm`: if `M` is killed by `𝔪` and the forms `g i` detect zero on `M`, their base
  changes detect zero on `k ⊗ M`.
- `smul_top_eq_bot_of_killed`: `𝔪 • ⊤ = ⊥` in a module killed by `𝔪`.
- `eq_zero_of_pform`: let `M` be killed by `𝔪`. If the forms `g i` detect zero on `M` and the `h j`
  detect zero on `N`, and all `pform (g i) (h j) y` vanish, then `y = 0`. The proof applies
  Mathlib's `detects_tensor` to `1 ⊗ y` in `k ⊗ (M ⊗ N)` and uses `1 ⊗ y = 0 ↔ y ∈ 𝔪 • ⊤`.

## The maximal locus

For a family `F i : C →ₗ[R] R` of `R`-valued forms:

- `maxLocus F` is the submodule of `c` with `F i c ∈ 𝔪` for all `i` (`mem_maxLocus`).
- `quotForm F i : C ⧸ maxLocus F →ₗ[R] k` is the reduction of `F i` (`quotForm_mk`).
- `quot_killed` and `quot_detects`: the quotient `C ⧸ maxLocus F` is killed by `𝔪`, and the forms
  `quotForm F i` detect zero on it.
- `mem_sup_of_productForm` (**tensor density**): let `x ∈ C ⊗[R] D`. Suppose every product form
  `productForm (F i) (G j)` (from `Smoothening.TensorDensity`) takes `x` into `𝔪`. Then `x` lies in
  `C ⊗ maxLocus G + maxLocus F ⊗ D`, written as the sum of the ranges of `lTensor` and `rTensor`
  of the inclusions.

  Proof: by right exactness of the tensor product (`TensorProduct.map_ker`), the sum is the kernel
  of `C ⊗ D → (C ⧸ maxLocus F) ⊗ (D ⧸ maxLocus G)`. The image of `x` there vanishes by
  `eq_zero_of_pform` applied to the forms `quotForm`.

This generalizes `DetectsMaximal.tensor`, which is the case `maxLocus F = 𝔪 C`.
