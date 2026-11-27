import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Algebra.DualNumber

/-! # Determinants of matrices over dual numbers that reduce to the identity

If a square matrix `M` over the dual numbers `A[ε]` reduces to the identity modulo `ε`, then
`det M = 1 + ε · tr N`, where `N` is the matrix of `ε`-coefficients of `M`. -/

namespace Langlands.Algebra.DualNumberDeterminant

open Polynomial Matrix TrivSqZeroExt

variable {A : Type*} [CommRing A] {n : Type*} [Fintype n] [DecidableEq n]

/-- A matrix over `A[ε]` that reduces to the identity has determinant `1 + ε · tr N`, where
`N` is its matrix of `ε`-coefficients. -/
theorem det_eq_of_map_fst_eq_one (M : Matrix n n (DualNumber A)) (hM : M.map fst = 1) :
    M.det = inl 1 + inr (trace (M.map snd)) := by
  let e : A[X] →ₐ[A] DualNumber A := aeval DualNumber.eps
  have he (p : A) : e (C p) = inl p := by
    change aeval DualNumber.eps (C p) = _
    rw [aeval_C]
    rfl
  have hX : e X = DualNumber.eps := aeval_X _
  have hone (i k : n) : e ((1 : Matrix n n A[X]) i k) = inl ((1 : Matrix n n A) i k) := by
    by_cases hik : i = k
    · subst hik
      rw [Matrix.one_apply_eq, Matrix.one_apply_eq, map_one, inl_one]
    · rw [Matrix.one_apply_ne hik, Matrix.one_apply_ne hik, map_zero, inl_zero]
  have hentry : M = e.toRingHom.mapMatrix (1 + (X : A[X]) • (M.map snd).map C) := by
    ext i k : 1
    have h1 : (M i k).fst = (1 : Matrix n n A) i k := congrFun (congrFun hM i) k
    change M i k = e ((1 : Matrix n n A[X]) i k + X * C (M i k).snd)
    rw [map_add, map_mul, hX, he, hone]
    apply TrivSqZeroExt.ext
    · rw [fst_add, fst_inl, fst_mul, DualNumber.fst_eps, zero_mul, add_zero, h1]
    · rw [snd_add, snd_inl, snd_mul, DualNumber.fst_eps, DualNumber.snd_eps, snd_inl, fst_inl,
        zero_smul, zero_add, zero_add, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, one_mul]
  have hdet : M.det = e (det (1 + (X : A[X]) • (M.map snd).map C)) := by
    conv_lhs => rw [hentry]
    exact (RingHom.map_det e.toRingHom _).symm
  rw [hdet, det_one_add_X_smul]
  rw [map_add, map_add, map_one, map_mul, map_pow, map_smul, hX, pow_two, DualNumber.eps_mul_eps,
    mul_zero, add_zero]
  apply TrivSqZeroExt.ext
  · rw [fst_add, fst_one, fst_smul, DualNumber.fst_eps, smul_zero, add_zero, fst_add, fst_inl,
      fst_inr, add_zero]
  · rw [snd_add, snd_one, snd_smul, DualNumber.snd_eps, smul_eq_mul, mul_one, zero_add, snd_add,
      snd_inl, snd_inr, zero_add]

end Langlands.Algebra.DualNumberDeterminant
