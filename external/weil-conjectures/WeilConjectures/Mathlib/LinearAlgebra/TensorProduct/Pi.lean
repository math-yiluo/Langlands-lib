/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Coordinates in `M ⊗ R^n`

Formulas for the coordinates `TensorProduct.piScalarRight` of elements of `M ⊗[R] (Fin n → R)`:
after applying a matrix (`TensorProduct.piScalarRight_lTensor_mulVecLin`) and for sums of
`yⱼ ⊗ eⱼ` (`TensorProduct.piScalarRight_sum_tmul_single`).
-/

@[expose] public section

open scoped TensorProduct

namespace TensorProduct

/-- Coordinates of an element of `M ⊗ R^t` after applying the matrix `b`: the coordinates of
`(1 ⊗ b) z` are `∑ₘ bⱼₘ zₘ`, in terms of the coordinates `zₘ` of `z`. -/
lemma piScalarRight_lTensor_mulVecLin {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] {s t : ℕ} (b : Matrix (Fin s) (Fin t) R) (z : M ⊗[R] (Fin t → R))
    (j : Fin s) :
    TensorProduct.piScalarRight R R M (Fin s) ((b.mulVecLin).lTensor M z) j =
      ∑ m, b j m • TensorProduct.piScalarRight R R M (Fin t) z m := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy =>
    simp only [map_add, Pi.add_apply, hx, hy, smul_add, Finset.sum_add_distrib]
  | tmul x v =>
    simp [Matrix.mulVec, dotProduct, Finset.sum_smul, mul_smul]

/-- Coordinates of `∑ⱼ yⱼ ⊗ eⱼ` in `M ⊗ R^s` are the `yⱼ`. -/
lemma piScalarRight_sum_tmul_single {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] {s : ℕ} (y : Fin s → M) :
    TensorProduct.piScalarRight R R M (Fin s) (∑ j, y j ⊗ₜ Pi.single j 1) = y := by
  ext i
  simp [Pi.single_apply]

end TensorProduct
