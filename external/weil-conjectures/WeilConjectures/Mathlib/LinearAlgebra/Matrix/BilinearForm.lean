/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-!
# The dimension of a space carrying a nondegenerate alternating form is even

## Main results

- `LinearMap.BilinForm.even_finrank_of_isAlt` — a finite-dimensional vector space over a field
  of characteristic different from `2` carrying a nondegenerate alternating bilinear form has even
  dimension (blueprint `corollary-functional-equation--5`).
-/

@[expose] public section

open Matrix

namespace LinearMap.BilinForm

variable {K V : Type*} [Field K] [NeZero (2 : K)] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

/-- Blueprint `corollary-functional-equation--5`: over a field of characteristic different
from `2`, a nondegenerate alternating bilinear form on a finite-dimensional vector space forces the
dimension to be even: the Gram matrix `M` of the form in any basis is skew-symmetric, so
`det M = det Mᵀ = (-1) ^ dim V * det M`, and `det M ≠ 0` by nondegeneracy. -/
theorem even_finrank_of_isAlt {B : LinearMap.BilinForm K V} (halt : B.IsAlt)
    (hnd : B.Nondegenerate) : Even (Module.finrank K V) := by
  classical
  by_contra hodd
  rw [Nat.not_even_iff_odd] at hodd
  set b := Module.finBasis K V with hb
  set M := LinearMap.BilinForm.toMatrix b B with hM
  have hskew : Mᵀ = -M := by
    ext i j
    simp only [Matrix.transpose_apply, Matrix.neg_apply, hM, LinearMap.BilinForm.toMatrix_apply]
    exact (halt.neg_eq _ _).symm
  have hdet : M.det = -M.det := by
    conv_lhs => rw [← Matrix.det_transpose M, hskew, Matrix.det_neg]
    rw [Fintype.card_fin, hodd.neg_one_pow, neg_one_mul]
  have h2 : (2 : K) * M.det = 0 := by
    rw [two_mul]
    nth_rewrite 2 [hdet]
    ring
  have hzero : M.det = 0 := (mul_eq_zero.1 h2).resolve_left two_ne_zero
  exact ((nondegenerate_iff_det_ne_zero b).1 hnd) hzero

end LinearMap.BilinForm

end
