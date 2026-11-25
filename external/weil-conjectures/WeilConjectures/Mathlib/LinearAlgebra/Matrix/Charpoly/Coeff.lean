/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import WeilConjectures.Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-!
# The reverse characteristic polynomial of a matrix inverse

If `A * B = c • 1`, then `det (1 - t • B)` is determined by the characteristic polynomial of
`A`: `det A * det (1 - t • B) = (-1) ^ n * det (c * t - A)`.
-/

@[expose] public section

open Polynomial

namespace Matrix

variable {R : Type*} [CommRing R] {n : Type*} [DecidableEq n] [Fintype n]

/-- If `A * B = c • 1`, then the reverse characteristic polynomial of `B` is determined by the
characteristic polynomial of `A`. -/
theorem C_det_mul_charpolyRev {A B : Matrix n n R} {c : R} (h : A * B = c • 1) :
    C A.det * B.charpolyRev = C ((-1) ^ Fintype.card n) * A.charpoly.comp (C c * X) := by
  have hmap : A.map C * B.map C = Matrix.scalar n (C c) := by
    rw [← Matrix.map_mul, h]
    ext i j
    by_cases hij : i = j <;> simp [hij, Matrix.scalar_apply]
  have key : A.map C * (1 - (X : R[X]) • B.map C) = -(Matrix.scalar n (C c * X) - A.map C) := by
    have hsmul : (X : R[X]) • Matrix.scalar n (C c) = Matrix.scalar n (C c * X) := by
      rw [Matrix.smul_eq_diagonal_mul, ← Matrix.scalar_apply, ← map_mul, mul_comm]
    rw [mul_sub, mul_one, mul_smul_comm, hmap, hsmul, neg_sub]
  have hdet := congrArg Matrix.det key
  rw [Matrix.det_mul, det_neg, ← charpolyRev, ← charpoly_comp] at hdet
  rw [show C A.det = (A.map (C : R →+* R[X])).det by rw [RingHom.map_det]; rfl, map_pow, map_neg,
    map_one]
  exact hdet

end Matrix
