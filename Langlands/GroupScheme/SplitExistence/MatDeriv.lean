import Langlands.GroupScheme.SplitExistence.LieConj

/-! # Derivatives of matrices over a polynomial ring

The entrywise derivative `mderiv` of square matrices over `A[X]`: it satisfies the Leibniz
rule, a matrix with zero derivative and value `1` at `X = 0` equals `1` (when `A` is
torsion-free), every polynomial over a `ℚ`-algebra has an antiderivative vanishing at `0`, and
the root exponential satisfies `x_k(f)' = f' • E_k x_k(f)`. -/

noncomputable section

universe u

open Matrix Finset Polynomial

namespace Langlands.GroupScheme.SplitExistence

variable {m : Type*} {A : Type*} [CommRing A]

/-- The entrywise derivative of a matrix over `A[X]`. -/
def mderiv (M : Matrix m m A[X]) : Matrix m m A[X] :=
  M.map fun p => derivative p

@[simp]
theorem mderiv_apply (M : Matrix m m A[X]) (c d : m) : mderiv M c d = derivative (M c d) :=
  rfl

theorem mderiv_add (M N : Matrix m m A[X]) : mderiv (M + N) = mderiv M + mderiv N := by
  ext c d
  simp

theorem mderiv_mul [Fintype m] (M N : Matrix m m A[X]) :
    mderiv (M * N) = mderiv M * N + M * mderiv N := by
  ext c d
  simp [Matrix.mul_apply, derivative_mul, Finset.sum_add_distrib]

theorem mderiv_smul (f : A[X]) (M : Matrix m m A[X]) :
    mderiv (f • M) = derivative f • M + f • mderiv M := by
  ext c d
  simp [derivative_mul]

theorem mderiv_sum {ι : Type*} (s : Finset ι) (M : ι → Matrix m m A[X]) :
    mderiv (∑ i ∈ s, M i) = ∑ i ∈ s, mderiv (M i) := by
  ext c d
  simp [Matrix.sum_apply]

theorem mderiv_map_intCast (M : Matrix m m ℤ) : mderiv (M.map (Int.castRingHom A[X])) = 0 := by
  ext c d
  simp

/-- A matrix with zero derivative and value `1` at `X = 0` is `1`. -/
theorem eq_one_of_mderiv_eq_zero [DecidableEq m] [IsAddTorsionFree A] {c : Matrix m m A[X]}
    (hc : mderiv c = 0) (h0 : c.map (evalRingHom 0) = 1) : c = 1 := by
  ext a b
  have hd : derivative (c a b) = 0 := by
    simpa using congrFun (congrFun hc a) b
  have he : (c a b).eval 0 = (1 : Matrix m m A) a b := by
    simpa using congrFun (congrFun h0 a) b
  rw [eq_C_of_derivative_eq_zero hd, coeff_zero_eq_eval_zero, he, Matrix.one_apply,
    Matrix.one_apply]
  split_ifs <;> simp

/-- Every polynomial over a `ℚ`-algebra has an antiderivative with constant term `0`. -/
theorem exists_antideriv [Algebra ℚ A] (p : A[X]) :
    ∃ F : A[X], derivative F = p ∧ F.coeff 0 = 0 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨F, hF, hF0⟩ := hp
    obtain ⟨G, hG, hG0⟩ := hq
    exact ⟨F + G, by rw [derivative_add, hF, hG], by rw [coeff_add, hF0, hG0, add_zero]⟩
  | monomial i a =>
    refine ⟨monomial (i + 1) (algebraMap ℚ A ((i + 1 : ℕ) : ℚ)⁻¹ * a), ?_, ?_⟩
    · rw [derivative_monomial, Nat.add_sub_cancel, mul_right_comm,
        ← map_natCast (algebraMap ℚ A), ← map_mul, inv_mul_cancel₀ (by positivity), map_one,
        one_mul]
    · simp [coeff_monomial]

namespace LieRootData

variable {J X Y : Type u} [AddCommGroup X] [AddCommGroup Y] {P : RootDatum J X Y}
  (D : LieRootData P)

theorem mderiv_em (k : J) (i : ℕ) : mderiv (D.em A[X] k i) = 0 :=
  mderiv_map_intCast _

/-- The derivative of a root exponential: `x_k(f)' = f' • E_k x_k(f)`. -/
theorem mderiv_divExp (k : J) (f : A[X]) :
    mderiv (divExp (D.e k) f) = derivative f • (D.E A[X] k * divExp (D.e k) f) := by
  rw [divExp_eq, mderiv_sum, Finset.mul_sum, Finset.smul_sum, Finset.sum_range_succ',
    Finset.sum_range_succ]
  simp only [mderiv_smul, mderiv_em, smul_zero, add_zero, pow_zero, derivative_one, zero_smul,
    Matrix.mul_smul, E_mul_em, smul_smul, D.em_eq_zero k (Nat.lt_add_one D.n)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [derivative_pow_succ, map_add, map_natCast, map_one]
  congr 1
  push_cast
  ring

end LieRootData

end Langlands.GroupScheme.SplitExistence
