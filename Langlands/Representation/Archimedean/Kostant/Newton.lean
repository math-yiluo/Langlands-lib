import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.RingTheory.MatrixPolynomialAlgebra

/-!
# Newton's identities for the characteristic polynomial of a matrix

For a square matrix `M` of size `N` over a commutative ring, with characteristic polynomial
`χ = ∑ c_j t^{N-j}` (`c_0 = 1`), Newton's identities read
`k c_k + ∑_{j<k} c_j tr(M^{k-j}) = 0` for `1 ≤ k ≤ N`.

The proof is the Faddeev–LeVerrier argument. The derivative of a determinant is the sum of the
determinants with one column differentiated, so `χ' = tr adj(t - M)`. Writing
`adj(t - M) = ∑_m Q_m t^m`, the identity `(t - M) adj(t - M) = χ` gives
`Q_m = M Q_{m+1} + χ_{m+1}` and `M Q_0 + χ_0 = 0`, hence
`Q_{N-1-k} = ∑_{j ≤ k} c_j M^{k-j}`; comparing traces gives the identities.
-/

noncomputable section

set_option autoImplicit false

open Polynomial Matrix

namespace Langlands.Archimedean.Kostant

variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]

/-- Jacobi's rule: the derivative of a determinant of polynomials is the sum of the
determinants with one column differentiated. -/
theorem derivative_det (A : Matrix n n R[X]) :
    derivative A.det = ∑ i, (A.updateCol i fun r => derivative (A r i)).det := by
  simp only [det_apply, map_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Units.smul_def, map_zsmul, derivative_prod_finset, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Units.smul_def]
  congr 1
  rw [← Finset.prod_erase_mul Finset.univ
    (fun x => (A.updateCol i fun r => derivative (A r i)) (σ x) x) (Finset.mem_univ i)]
  congr 1
  · refine Finset.prod_congr rfl fun j hj => ?_
    simp [Finset.ne_of_mem_erase hj]
  · simp

theorem derivative_charpoly (M : Matrix n n R) :
    derivative M.charpoly = trace (adjugate (charmatrix M)) := by
  rw [charpoly, derivative_det]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hcol : (fun r => derivative (charmatrix M r i)) = Pi.single i 1 := by
    funext r
    by_cases h : r = i
    · subst h; simp [charmatrix_apply_eq]
    · rw [charmatrix_apply_ne _ _ _ h, Pi.single_apply, ite_eq_right h]; simp
  rw [hcol, ← cramer_apply, cramer_eq_adjugate_mulVec, mulVec_single_one]
  rfl

/-- The coefficient matrices of `adj(t - M)`. -/
def adjCoeff (M : Matrix n n R) (m : ℕ) : Matrix n n R :=
  (matPolyEquiv (adjugate (charmatrix M))).coeff m

theorem adjCoeff_rel (M : Matrix n n R) :
    (X - C M) * matPolyEquiv (adjugate (charmatrix M)) =
      matPolyEquiv (M.charpoly • (1 : Matrix n n R[X])) := by
  rw [← matPolyEquiv_charmatrix, ← map_mul, mul_adjugate]
  rfl

theorem coeff_matPolyEquiv_smul_one (p : R[X]) (m : ℕ) :
    (matPolyEquiv (p • (1 : Matrix n n R[X]))).coeff m = p.coeff m • (1 : Matrix n n R) := by
  ext i j
  rw [matPolyEquiv_coeff_apply]
  by_cases h : i = j
  · subst h; simp
  · simp [h]

theorem adjCoeff_succ (M : Matrix n n R) (m : ℕ) :
    adjCoeff M m = M * adjCoeff M (m + 1) + M.charpoly.coeff (m + 1) • (1 : Matrix n n R) := by
  have h := congrArg (fun q => q.coeff (m + 1)) (adjCoeff_rel M)
  simp only [sub_mul, coeff_sub, coeff_X_mul, coeff_C_mul, coeff_matPolyEquiv_smul_one] at h
  rw [adjCoeff, adjCoeff, ← h]
  abel

theorem adjCoeff_zero (M : Matrix n n R) :
    M * adjCoeff M 0 + M.charpoly.coeff 0 • (1 : Matrix n n R) = 0 := by
  have h := congrArg (fun q => q.coeff 0) (adjCoeff_rel M)
  simp only [sub_mul, coeff_sub, coeff_X_mul_zero, coeff_C_mul,
    coeff_matPolyEquiv_smul_one, zero_sub] at h
  rw [adjCoeff, ← h]
  abel

theorem trace_adjCoeff (M : Matrix n n R) (m : ℕ) :
    trace (adjCoeff M m) = M.charpoly.coeff (m + 1) * (m + 1) := by
  have h := congrArg (fun q => q.coeff m) (derivative_charpoly M)
  simp only [coeff_derivative] at h
  rw [h, trace, trace, finsetSum_coeff]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact matPolyEquiv_coeff_apply _ _ _ _

theorem adjCoeff_eq_zero (M : Matrix n n R) {m : ℕ} (hm : Fintype.card n ≤ m) :
    adjCoeff M m = 0 := by
  nontriviality R
  have hdeg : ∀ k, Fintype.card n < k → M.charpoly.coeff k = 0 := fun k hk =>
    coeff_eq_zero_of_natDegree_lt (by rwa [charpoly_natDegree_eq_dim])
  set D := (matPolyEquiv (adjugate (charmatrix M))).natDegree
  have key : ∀ t m, Fintype.card n ≤ m → D < m + t → adjCoeff M m = 0 := by
    intro t
    induction t with
    | zero => intro m _ h; exact coeff_eq_zero_of_natDegree_lt (by omega)
    | succ t ih =>
      intro m hm h
      rw [adjCoeff_succ, ih (m + 1) (by omega) (by omega), hdeg (m + 1) (by omega), mul_zero,
        zero_smul, add_zero]
  exact key (D + 1) m hm (by omega)

/-- The closed form `Q_{N-1-k} = ∑_{j ≤ k} c_j M^{k-j}`, `c_j = χ_{N-j}`. -/
theorem adjCoeff_eq_sum (M : Matrix n n R) (k : ℕ) (hk : k < Fintype.card n) :
    adjCoeff M (Fintype.card n - 1 - k) =
      ∑ j ∈ Finset.range (k + 1), M.charpoly.coeff (Fintype.card n - j) • M ^ (k - j) := by
  nontriviality R
  induction k with
  | zero =>
    rw [adjCoeff_succ, show Fintype.card n - 1 - 0 + 1 = Fintype.card n by omega,
      adjCoeff_eq_zero M le_rfl, mul_zero, zero_add]
    have := (charpoly_monic M).coeff_natDegree
    rw [charpoly_natDegree_eq_dim] at this
    simp [this]
  | succ k ih =>
    rw [adjCoeff_succ, show Fintype.card n - 1 - (k + 1) + 1 = Fintype.card n - 1 - k by omega,
      ih (by omega), Finset.sum_range_succ _ (k + 1), Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun j hj => ?_
      rw [Finset.mem_range] at hj
      rw [mul_smul_comm, ← pow_succ', show k + 1 - j = k - j + 1 by omega]
    · rw [Nat.sub_self, pow_zero, show Fintype.card n - 1 - k = Fintype.card n - (k + 1) by
        omega]

/-- Newton's identities: `k c_k + ∑_{j<k} c_j tr(M^{k-j}) = 0` for `k ≤ N`, where
`c_j = χ_{N-j}` is the coefficient of `t^{N-j}` in the characteristic polynomial. -/
theorem newton_identity (M : Matrix n n R) (k : ℕ) (hk : k ≤ Fintype.card n) :
    (k : R) * M.charpoly.coeff (Fintype.card n - k) +
      ∑ j ∈ Finset.range k, M.charpoly.coeff (Fintype.card n - j) * trace (M ^ (k - j)) = 0 := by
  nontriviality R
  rcases Nat.eq_zero_or_pos k with rfl | hpos
  · simp
  rcases hk.lt_or_eq with hlt | heq
  · -- `k < N`: compare the trace of `Q_{N-1-k}` with the derivative of `χ`
    have h1 := trace_adjCoeff M (Fintype.card n - 1 - k)
    rw [adjCoeff_eq_sum M k hlt, trace_sum] at h1
    simp only [trace_smul, smul_eq_mul] at h1
    rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, trace_one,
      show Fintype.card n - 1 - k + 1 = Fintype.card n - k by omega] at h1
    have hcast : ((Fintype.card n - 1 - k : ℕ) : R) + 1 = (Fintype.card n : R) - k := by
      rw [show Fintype.card n - 1 - k = Fintype.card n - k - 1 by omega,
        Nat.cast_sub (by omega), Nat.cast_sub hk]
      simp
    rw [hcast] at h1
    linear_combination h1
  · -- `k = N`: the trace of Cayley–Hamilton
    subst heq
    have h0 := adjCoeff_zero M
    have hN : 0 < Fintype.card n := hpos
    rw [show (0 : ℕ) = Fintype.card n - 1 - (Fintype.card n - 1) by omega,
      adjCoeff_eq_sum M _ (by omega), Finset.mul_sum] at h0
    have ht := congrArg trace h0
    rw [trace_add, trace_sum, trace_smul, trace_one, trace_zero] at ht
    simp only [mul_smul_comm, trace_smul, smul_eq_mul, ← pow_succ'] at ht
    rw [show Fintype.card n - 1 + 1 = Fintype.card n by omega, Nat.sub_self] at ht
    have hsum : ∑ j ∈ Finset.range (Fintype.card n),
        M.charpoly.coeff (Fintype.card n - j) * trace (M ^ (Fintype.card n - 1 - j + 1)) =
        ∑ j ∈ Finset.range (Fintype.card n),
          M.charpoly.coeff (Fintype.card n - j) * trace (M ^ (Fintype.card n - j)) := by
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Finset.mem_range] at hj
      rw [show Fintype.card n - 1 - j + 1 = Fintype.card n - j by omega]
    rw [hsum] at ht
    rw [Nat.sub_self]
    linear_combination ht

end Langlands.Archimedean.Kostant
