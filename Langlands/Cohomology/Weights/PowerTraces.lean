import Langlands.Cohomology.Weights.PowerSums
import Langlands.Automorphic.AssociatedGammaTriangular
import Mathlib.LinearAlgebra.Trace

/-! # Power traces after a complex realization -/

noncomputable section

open Polynomial
open scoped BigOperators

set_option autoImplicit false

namespace Langlands.Cohomology.Weights

private theorem trace_pow_eq_rootPowerSum_of_upperTriangular {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsUpperTriangular) (k : ℕ) :
    (A ^ k).trace = rootPowerSum A.charpoly k := by
  classical
  have hdiag (k : ℕ) (i : Fin n) : (A ^ k) i i = A i i ^ k := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, Matrix.mul_apply, Finset.sum_eq_single i, ih, pow_succ]
      · intro j _ hji
        rcases lt_or_gt_of_ne hji with hj | hj
        · rw [hA.pow k hj, zero_mul]
        · rw [hA hj, mul_zero]
      · simp
  have hroots : A.charpoly.roots = Finset.univ.val.map (fun i => A i i) := by
    rw [Matrix.charpoly, Matrix.det_of_isUpperTriangular hA.charmatrix]
    simp only [Matrix.charmatrix_apply_eq]
    rw [Finset.prod_eq_multiset_prod]
    have hmap : (Finset.univ.val.map fun i : Fin n => X - C (A i i)) =
        (Finset.univ.val.map fun i : Fin n => A i i).map (fun a => X - C a) := by
      rw [Multiset.map_map]
      rfl
    rw [hmap, roots_multiset_prod_X_sub_C]
  simp only [Matrix.trace, Matrix.diag_apply, hdiag, rootPowerSum, hroots, Multiset.map_map]
  rfl

private theorem trace_pow_eq_rootPowerSum_of_unit {n : ℕ}
    (u : (Matrix (Fin n) (Fin n) ℂ)ˣ) (k : ℕ) :
    ((u : Matrix (Fin n) (Fin n) ℂ) ^ k).trace =
      rootPowerSum (u : Matrix (Fin n) (Fin n) ℂ).charpoly k := by
  let A : Matrix (Fin n) (Fin n) ℂ := u
  let r : Multiplicative ℤ →* Matrix (Fin n) (Fin n) ℂ :=
    (Units.coeHom _).comp (zpowersHom _ u)
  obtain ⟨P, Q, hPQ, htri⟩ := Langlands.LieKolchin.exists_triangularizing_cyclic n r
  let B := Q * A * P
  have hB : B.IsUpperTriangular := by
    intro i j hij
    have hr : r (Multiplicative.ofAdd (1 : ℤ)) = A := by
      simp [r, A, zpowersHom_apply, Units.coeHom_apply]
    simpa only [hr] using htri (Multiplicative.ofAdd 1) i j hij
  have hpow : ∀ k : ℕ, B ^ k = Q * A ^ k * P := by
    intro k
    induction k with
    | zero => simp [mul_eq_one_comm.mp hPQ]
    | succ k ih =>
      rw [pow_succ, ih, show B = Q * A * P from rfl]
      simp only [mul_assoc]
      rw [← mul_assoc P Q, hPQ, one_mul, ← mul_assoc (A ^ k) A, ← pow_succ]
  have hchar : B.charpoly = A.charpoly := by
    dsimp only [B]
    rw [Matrix.charpoly_mul_comm (Q * A) P, ← mul_assoc, hPQ, one_mul]
  have htr : (B ^ k).trace = (A ^ k).trace := by
    rw [hpow, Matrix.trace_mul_comm (Q * A ^ k) P, ← mul_assoc, hPQ, one_mul]
  exact htr.symm.trans ((trace_pow_eq_rootPowerSum_of_upperTriangular B hB k).trans
    (congrArg (fun p => rootPowerSum p k) hchar))

/-- The trace of `A^k` transported through a field embedding into `ℂ`. -/
def complexPowerTrace {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (j : K →+* ℂ) (A : Module.End K V) (k : ℕ) : ℂ :=
  j (LinearMap.trace K V (A ^ k))

/-- The complex power trace of an invertible operator is the power sum of the roots of its
complex characteristic polynomial, counted with algebraic multiplicity. -/
theorem complexPowerTrace_eq_rootPowerSum {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (j : K →+* ℂ) (A : Module.End K V) (hA : IsUnit A) (k : ℕ) :
    complexPowerTrace j A k = rootPowerSum (A.charpoly.map j) k := by
  classical
  let b := Module.finBasis K V
  let f := LinearMap.toMatrixAlgEquiv b
  let g := j.mapMatrix (m := Fin (Module.finrank K V))
  have hunit : IsUnit (g (f A)) := (hA.map f.toMonoidHom).map g.toMonoidHom
  obtain ⟨u, hu⟩ := hunit
  have heq := trace_pow_eq_rootPowerSum_of_unit u k
  rw [hu] at heq
  rw [complexPowerTrace, LinearMap.trace_eq_matrix_trace K b, ← LinearMap.charpoly_toMatrix A b]
  change j (Matrix.trace (f (A ^ k))) = rootPowerSum ((f A).charpoly.map j) k
  rw [map_pow, AddMonoidHom.map_trace, ← Matrix.charpoly_map]
  change (g (f A ^ k)).trace = rootPowerSum (g (f A)).charpoly k
  rw [map_pow]
  exact heq

/-- An invertible operator has characteristic polynomial with nonzero constant term. -/
theorem charpoly_eval_zero_ne_zero_of_isUnit {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (A : Module.End K V) (hA : IsUnit A) : A.charpoly.eval 0 ≠ 0 := by
  classical
  let b := Module.finBasis K V
  rw [← LinearMap.charpoly_toMatrix A b, Matrix.eval_charpoly, map_zero, zero_sub, Matrix.det_neg]
  apply mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
  exact ((hA.map (LinearMap.toMatrixAlgEquiv b).toMonoidHom).map (Matrix.detMonoidHom)).ne_zero

end Langlands.Cohomology.Weights
