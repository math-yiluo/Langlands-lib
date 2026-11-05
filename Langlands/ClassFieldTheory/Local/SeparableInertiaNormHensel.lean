import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Data.NNReal.Basic
import Mathlib.RingTheory.Valuation.Basic

/-! # Valuation-theoretic Hensel lemmas over a field with a real valuation

Abstract hypotheses used by the proof of norm surjectivity over the separable inertia fixed
field: simple-root Hensel lifting, root finding modulo the maximal ideal, and uniformizers,
all phrased for a valuation `v : Valuation K ℝ≥0` on a field `K`. The main result is a
strong Hensel lemma for polynomials whose linear coefficient is `1` and whose constant
coefficient is small, deduced from the simple-root form by reversing a polynomial.
-/

noncomputable section

open Polynomial Finset
open scoped NNReal

namespace Langlands.ClassFieldTheory.Local.SeparableInertiaNorm

variable {K : Type*} [Field K] (v : Valuation K ℝ≥0)

/-- Simple-root Hensel lifting for the integers `{x | v x ≤ 1}` of `v`. -/
def ValHensel : Prop :=
  ∀ f : K[X], f.Monic → (∀ i, v (f.coeff i) ≤ 1) → ∀ a₀ : K, v a₀ ≤ 1 →
    v (f.eval a₀) < 1 → v (f.derivative.eval a₀) = 1 →
      ∃ a : K, f.eval a = 0 ∧ v (a - a₀) < 1

/-- Root finding modulo the maximal ideal: an integral polynomial with a unit coefficient in
positive degree has an integral root modulo the maximal ideal. This holds when the residue
field of `v` is algebraically closed. -/
def ValResidueRoot : Prop :=
  ∀ f : K[X], (∀ i, v (f.coeff i) ≤ 1) → (∃ i, 0 < i ∧ v (f.coeff i) = 1) →
    ∃ b : K, v b ≤ 1 ∧ v (f.eval b) < 1

/-- `π` is a uniformizer for `v`: its value lies strictly between `0` and `1` and every
nonzero integral element has value a natural power of `v π`. -/
def ValUniformizer (π : K) : Prop :=
  0 < v π ∧ v π < 1 ∧ ∀ b : K, b ≠ 0 → v b ≤ 1 → ∃ k : ℕ, v b = v π ^ k

/-- Polynomials with integral coefficients. -/
def IntPoly (f : K[X]) : Prop := ∀ i, v (f.coeff i) ≤ 1

variable {v}

theorem IntPoly.add {f g : K[X]} (hf : IntPoly v f) (hg : IntPoly v g) : IntPoly v (f + g) :=
  fun i => by rw [coeff_add]; exact v.map_add_le (hf i) (hg i)

theorem IntPoly.sum {ι : Type*} (s : Finset ι) {f : ι → K[X]} (hf : ∀ k ∈ s, IntPoly v (f k)) :
    IntPoly v (∑ k ∈ s, f k) :=
  fun i => by
    rw [finsetSum_coeff]
    exact v.map_sum_le fun k hk => hf k hk i

theorem IntPoly.C_mul_X_pow {a : K} (ha : v a ≤ 1) (n : ℕ) : IntPoly v (C a * X ^ n) :=
  fun i => by
    rw [coeff_C_mul_X_pow]
    split_ifs
    · exact ha
    · simp

theorem IntPoly.X_pow (n : ℕ) : IntPoly v (X ^ n : K[X]) := by
  simpa using IntPoly.C_mul_X_pow (v := v) (a := 1) (by simp) n

theorem val_eval_le_one {f : K[X]} (hf : IntPoly v f) {a : K} (ha : v a ≤ 1) :
    v (f.eval a) ≤ 1 := by
  rw [eval_eq_sum_range]
  apply v.map_sum_le
  intro i _
  rw [map_mul, map_pow]
  exact mul_le_one' (hf i) (pow_le_one' ha i)

theorem val_sum_mul_pow_le_one {ι : Type*} (s : Finset ι) {c : ι → K} {e : ι → ℕ}
    (hc : ∀ k ∈ s, v (c k) ≤ 1) {a : K} (ha : v a ≤ 1) :
    v (∑ k ∈ s, c k * a ^ e k) ≤ 1 :=
  v.map_sum_le fun k hk => by
    rw [map_mul, map_pow]
    exact mul_le_one' (hc k hk) (pow_le_one' ha _)

theorem val_neg_one : v (-1 : K) = 1 := by
  rw [Valuation.map_neg, map_one]

theorem val_natCast_le_one (m : ℕ) : v (m : K) ≤ 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.cast_succ]
    exact v.map_add_le ih (by rw [map_one])

/-- The reversed polynomial used in the strong Hensel lemma. -/
private def revPoly (N n : ℕ) (a0 : K) (c : ℕ → K) : K[X] :=
  X ^ N + X ^ (N - 1) + ∑ k ∈ Ico 2 n, C (a0 * (c k * a0 ^ (k - 2))) * X ^ (N - k)

private theorem revPoly_monic (n : ℕ) (a0 : K) (c : ℕ → K) :
    (revPoly (n + 2) n a0 c).Monic := by
  unfold revPoly
  have hdeg : (X ^ (n + 2 - 1) + ∑ k ∈ Ico 2 n, C (a0 * (c k * a0 ^ (k - 2))) *
      X ^ (n + 2 - k) : K[X]).degree < (X ^ (n + 2) : K[X]).degree := by
    rw [degree_X_pow]
    refine lt_of_le_of_lt (degree_add_le _ _) (max_lt ?_ ?_)
    · rw [degree_X_pow]
      exact_mod_cast (by omega : n + 2 - 1 < n + 2)
    · refine lt_of_le_of_lt (degree_sum_le _ _) ?_
      refine (Finset.sup_lt_iff (WithBot.bot_lt_coe _)).mpr fun k hk => ?_
      refine lt_of_le_of_lt (degree_C_mul_X_pow_le _ _) ?_
      have hk2 := (mem_Ico.mp hk).1
      exact_mod_cast (by omega : n + 2 - k < n + 2)
  rw [add_assoc]
  exact (monic_X_pow _).add_of_left hdeg

private theorem revPoly_intPoly (N n : ℕ) {a0 : K} (ha0 : v a0 ≤ 1) {c : ℕ → K}
    (hc : ∀ k, v (c k) ≤ 1) : IntPoly v (revPoly N n a0 c) := by
  unfold revPoly
  refine ((IntPoly.X_pow N).add (IntPoly.X_pow (N - 1))).add
    (IntPoly.sum _ fun k _ => IntPoly.C_mul_X_pow ?_ _)
  rw [map_mul, map_mul, map_pow]
  exact mul_le_one' ha0 (mul_le_one' (hc k) (pow_le_one' ha0 _))

private theorem revPoly_eval (N n : ℕ) (a0 : K) (c : ℕ → K) (W : K) :
    (revPoly N n a0 c).eval W =
      W ^ N + W ^ (N - 1) + a0 * ∑ k ∈ Ico 2 n, c k * a0 ^ (k - 2) * W ^ (N - k) := by
  unfold revPoly
  simp only [eval_add, eval_pow, eval_X, eval_finsetSum, eval_mul, eval_C, mul_sum]
  congr 1
  exact sum_congr rfl fun k _ => by ring

private theorem revPoly_derivative_eval (N n : ℕ) (a0 : K) (c : ℕ → K) (W : K) :
    (derivative (revPoly N n a0 c)).eval W =
      (N : K) * W ^ (N - 1) + ((N - 1 : ℕ) : K) * W ^ (N - 1 - 1) +
        a0 * ∑ k ∈ Ico 2 n, c k * a0 ^ (k - 2) * ((N - k : ℕ) : K) * W ^ (N - k - 1) := by
  unfold revPoly
  simp only [derivative_add, derivative_X_pow, derivative_sum, derivative_C_mul_X_pow,
    eval_add, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, mul_sum]
  congr 1
  exact sum_congr rfl fun k _ => by ring

/-- Strong Hensel lemma: if `v a0 < 1` and the coefficients `c k` are integral, the equation
`a0 + y + ∑_{2 ≤ k < n} c k * y ^ k = 0` has a solution `y` with `v y < 1`. -/
theorem exists_root_one_add_of_hensel (hH : ValHensel v) (n : ℕ) {a0 : K} (ha0 : v a0 < 1)
    {c : ℕ → K} (hc : ∀ k, v (c k) ≤ 1) :
    ∃ y : K, v y < 1 ∧ a0 + y + ∑ k ∈ Ico 2 n, c k * y ^ k = 0 := by
  by_cases h0 : a0 = 0
  · refine ⟨0, by simp, ?_⟩
    rw [h0, zero_add, zero_add]
    refine sum_eq_zero fun k hk => ?_
    have : k ≠ 0 := by have := (mem_Ico.mp hk).1; omega
    simp [this]
  set N := n + 2 with hN
  have ha0' : v a0 ≤ 1 := ha0.le
  set R := revPoly N n a0 c with hR
  have hRint : IntPoly v R := revPoly_intPoly N n ha0' hc
  -- the error terms
  set s := ∑ k ∈ Ico 2 n, c k * a0 ^ (k - 2) * (-1 : K) ^ (N - k) with hs
  have hsv : v s ≤ 1 := by
    refine v.map_sum_le fun k _ => ?_
    rw [map_mul, map_mul, map_pow, map_pow, val_neg_one, one_pow, mul_one]
    exact mul_le_one' (hc k) (pow_le_one' ha0' _)
  have hRm1 : R.eval (-1) = a0 * s := by
    rw [hR, revPoly_eval]
    have : (-1 : K) ^ N + (-1) ^ (N - 1) = 0 := by
      rw [hN, show n + 2 - 1 = n + 1 by omega, pow_succ (-1 : K) (n + 1)]
      ring
    rw [this, zero_add]
  set s' := ∑ k ∈ Ico 2 n, c k * a0 ^ (k - 2) * ((N - k : ℕ) : K) * (-1 : K) ^ (N - k - 1)
    with hs'
  have hs'v : v s' ≤ 1 := by
    refine v.map_sum_le fun k _ => ?_
    rw [map_mul, map_mul, map_mul, map_pow, map_pow, val_neg_one, one_pow, mul_one]
    exact mul_le_one' (mul_le_one' (hc k) (pow_le_one' ha0' _)) (val_natCast_le_one _)
  have hd : (derivative R).eval (-1) = (-1) ^ (n + 1) + a0 * s' := by
    rw [hR, revPoly_derivative_eval, hN, show n + 2 - 1 = n + 1 by omega,
      show n + 1 - 1 = n by omega]
    push_cast
    ring
  have hdv : v ((derivative R).eval (-1)) = 1 := by
    rw [hd, Valuation.map_add_eq_of_lt_left, map_pow, val_neg_one, one_pow]
    rw [map_pow, val_neg_one, one_pow, map_mul]
    exact (mul_le_of_le_one_right (by positivity) hs'v).trans_lt ha0
  have hRv : v (R.eval (-1)) < 1 := by
    rw [hRm1, map_mul]
    exact (mul_le_of_le_one_right (by positivity) hsv).trans_lt ha0
  obtain ⟨W, hW, hWm⟩ := hH R (revPoly_monic n a0 c) hRint (-1) val_neg_one.le hRv hdv
  have hWv : v W = 1 := by
    have h1 : W = -1 + (W - -1) := by ring
    rw [h1, Valuation.map_add_eq_of_lt_left, val_neg_one]
    rwa [val_neg_one]
  have hW0 : W ≠ 0 := by
    intro h
    rw [h, map_zero] at hWv
    exact zero_ne_one hWv
  refine ⟨a0 / W, ?_, ?_⟩
  · rw [map_div₀, hWv, div_one]
    exact ha0
  have hWN : W ^ N ≠ 0 := pow_ne_zero _ hW0
  have hsum : W ^ N * ∑ k ∈ Ico 2 n, c k * (a0 / W) ^ k =
      a0 * (a0 * ∑ k ∈ Ico 2 n, c k * a0 ^ (k - 2) * W ^ (N - k)) := by
    rw [mul_sum, mul_sum, mul_sum]
    refine sum_congr rfl fun k hk => ?_
    have hk := mem_Ico.mp hk
    have hkN : W ^ N = W ^ (N - k) * W ^ k := by
      rw [← pow_add, show N - k + k = N by omega]
    have ha : a0 ^ k = a0 ^ 2 * a0 ^ (k - 2) := by
      rw [← pow_add, show 2 + (k - 2) = k by omega]
    rw [hkN, div_pow, ha]
    field_simp
  have key : W ^ N * (a0 + a0 / W + ∑ k ∈ Ico 2 n, c k * (a0 / W) ^ k) = a0 * R.eval W := by
    rw [hR, revPoly_eval, mul_add (W ^ N) (a0 + a0 / W), hsum, mul_add a0 _ (a0 * _)]
    congr 1
    have hN1 : W ^ N = W ^ (N - 1) * W := by
      rw [← pow_succ, show N - 1 + 1 = N by omega]
    rw [hN1]
    field_simp
  rw [hW, mul_zero] at key
  exact (mul_eq_zero.mp key).resolve_left hWN

end Langlands.ClassFieldTheory.Local.SeparableInertiaNorm
