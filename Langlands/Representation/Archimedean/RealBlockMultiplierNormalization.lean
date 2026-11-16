import Langlands.Representation.Archimedean.RealBlockMultiplierGeneric
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Complex.Basic

/-!
# Reciprocal generic multipliers and removal of one scalar pole

Internal algebra and analytic facts for the explicit finite products in
`RealBlockMultiplier`. No limiting intertwining operator is constructed here.
-/

noncomputable section

namespace Langlands.Archimedean.RealBlockMultiplier

open Finset

/-- Opposite parameters interchange the numerator and denominator of every factor.
This identity also holds at zeros, with Lean's totalized inverse. -/
theorem genericSeq_neg (ν : ℂ) (ε : ℤ) (m : ℕ) :
    genericSeq (-ν) ε m = (genericSeq ν ε m)⁻¹ := by
  simp only [genericSeq, ← Finset.prod_inv_distrib, inv_div, sub_neg_eq_add, ← sub_eq_add_neg]

theorem genericMultiplier_neg (ν : ℂ) (ε k : ℤ) :
    genericMultiplier (-ν) ε k = (genericMultiplier ν ε k)⁻¹ := by
  simp only [genericMultiplier, extend, genericSeq_neg]
  split_ifs
  · rfl
  · simp [mul_inv_rev, ← inv_pow, mul_comm]

theorem IsGenericParameter.neg {ν : ℂ} {ε : ℤ} (h : IsGenericParameter ν ε) :
    IsGenericParameter (-ν) ε := by
  constructor
  · intro m hm
    exact h.2 m (by linear_combination -hm)
  · intro m hm
    exact h.1 m (by linear_combination -hm)

theorem genericSeq_mul_neg {ν : ℂ} {ε : ℤ} (h : IsGenericParameter ν ε) (m : ℕ) :
    genericSeq ν ε m * genericSeq (-ν) ε m = 1 := by
  rw [genericSeq_neg]
  exact mul_inv_cancel₀ (genericSeq_ne_zero_of_ne h.1 h.2 m)

theorem genericMultiplier_mul_neg {ν : ℂ} {ε : ℤ}
    (h : IsGenericParameter ν ε) (k : ℤ) :
    genericMultiplier ν ε k * genericMultiplier (-ν) ε k = 1 := by
  rw [genericMultiplier_neg]
  exact mul_inv_cancel₀ (genericMultiplier_ne_zero_of_ne h.1 h.2 k)

/-- Analyticity at any parameter for which the finitely many denominators in this
particular sequence value are nonzero. -/
theorem analyticAt_genericSeq (ε : ℤ) (m : ℕ) {ν : ℂ}
    (hden : ∀ i < m, (ε : ℂ) + 2 * i + 1 + ν ≠ 0) :
    AnalyticAt ℂ (fun z => genericSeq z ε m) ν := by
  unfold genericSeq
  apply Finset.analyticAt_fun_prod
  intro i hi
  exact (analyticAt_const.sub analyticAt_id).div
    (analyticAt_const.add analyticAt_id) (hden i (Finset.mem_range.mp hi))

/-- A finite-product formula for `(ε + 2r + 1 + ν) genericSeq ν ε m`
in which the denominator at index `r` has been removed. -/
def regularizedSeq (ν : ℂ) (ε : ℤ) (r m : ℕ) : ℂ :=
  if r < m then
    ((ε : ℂ) + 2 * r + 1 - ν) *
      ∏ i ∈ (range m).erase r,
        ((ε : ℂ) + 2 * i + 1 - ν) / ((ε : ℂ) + 2 * i + 1 + ν)
  else
    ((ε : ℂ) + 2 * r + 1 + ν) * genericSeq ν ε m

/-- Away from the removed denominator's root, the regularized formula is the
generic product multiplied by that denominator. No other denominator hypothesis
is required for this algebraic identity. -/
theorem regularizedSeq_eq_mul_genericSeq {ν : ℂ} (ε : ℤ) (r m : ℕ)
    (hr : (ε : ℂ) + 2 * r + 1 + ν ≠ 0) :
    regularizedSeq ν ε r m =
      ((ε : ℂ) + 2 * r + 1 + ν) * genericSeq ν ε m := by
  unfold regularizedSeq
  split_ifs with hm
  · unfold genericSeq
    rw [← Finset.mul_prod_erase (range m) _ (Finset.mem_range.mpr hm)]
    field_simp
  · rfl

/-- The erased-product formula is analytic whenever all its remaining
denominators are nonzero. -/
theorem analyticAt_regularizedSeq (ε : ℤ) (r m : ℕ) {ν : ℂ}
    (hden : ∀ i < m, i ≠ r → (ε : ℂ) + 2 * i + 1 + ν ≠ 0) :
    AnalyticAt ℂ (fun z => regularizedSeq z ε r m) ν := by
  unfold regularizedSeq
  split_ifs with hm
  · apply (analyticAt_const.sub analyticAt_id).mul
    apply Finset.analyticAt_fun_prod
    intro i hi
    obtain ⟨hir, him⟩ := Finset.mem_erase.mp hi
    exact (analyticAt_const.sub analyticAt_id).div
      (analyticAt_const.add analyticAt_id) (hden i (Finset.mem_range.mp him) hir)
  · apply (analyticAt_const.add analyticAt_id).mul
    apply analyticAt_genericSeq
    intro i hi
    exact hden i hi (by omega)

/-- Distinct factor indices give distinct denominator roots. -/
theorem genericSeq_denom_at_pole_ne_zero (ε : ℤ) {r i : ℕ} (hi : i ≠ r) :
    (ε : ℂ) + 2 * i + 1 + -((ε : ℂ) + 2 * r + 1) ≠ 0 := by
  intro h
  have e : (i : ℂ) = r := by linear_combination (1 / 2 : ℂ) * h
  exact hi (by exact_mod_cast e)

/-- Each sequence coordinate has at most a simple pole at the exceptional
parameter `-(ε + 2r + 1)`: multiplication by its vanishing linear factor has
the analytic extension given by `regularizedSeq`. -/
theorem analyticAt_regularizedSeq_at_pole (ε : ℤ) (r m : ℕ) :
    AnalyticAt ℂ (fun z => regularizedSeq z ε r m)
      (-((ε : ℂ) + 2 * r + 1)) :=
  analyticAt_regularizedSeq ε r m fun _ _ hi =>
    genericSeq_denom_at_pole_ne_zero ε hi

theorem regularizedSeq_at_pole_eq_zero (ε : ℤ) {r m : ℕ} (hm : m ≤ r) :
    regularizedSeq (-((ε : ℂ) + 2 * r + 1)) ε r m = 0 := by
  simp [regularizedSeq, not_lt.mpr hm]

/-- Above the removed index, the regularized product satisfies the usual
recurrence whenever the new denominator is nonzero. -/
theorem regularizedSeq_succ_of_lt {ν : ℂ} (ε : ℤ) {r m : ℕ} (hm : r < m)
    (hden : (ε : ℂ) + 2 * m + 1 + ν ≠ 0) :
    regularizedSeq ν ε r (m + 1) * (ν + 1 + ε + 2 * m) =
      ((ε : ℂ) + 2 * m + 2 - (ν + 1)) * regularizedSeq ν ε r m := by
  have hm' : r < m + 1 := by omega
  have hmr : m ≠ r := by omega
  have hnot : m ∉ (range m).erase r := by simp
  simp only [regularizedSeq, hm, hm', ↓reduceIte, range_add_one, erase_insert_of_ne hmr]
  rw [prod_insert hnot]
  field_simp
  ring

theorem regularizedSeq_at_pole_succ (ε : ℤ) (r m : ℕ) :
    regularizedSeq (-((ε : ℂ) + 2 * r + 1)) ε r (m + 1) *
        (-((ε : ℂ) + 2 * r + 1) + 1 + ε + 2 * m) =
      ((ε : ℂ) + 2 * m + 2 - (-((ε : ℂ) + 2 * r + 1) + 1)) *
        regularizedSeq (-((ε : ℂ) + 2 * r + 1)) ε r m := by
  rcases lt_trichotomy m r with hm | rfl | hm
  · rw [regularizedSeq_at_pole_eq_zero ε (by omega),
      regularizedSeq_at_pole_eq_zero ε (by omega)]
    ring
  · rw [regularizedSeq_at_pole_eq_zero ε le_rfl]
    have hz : -((ε : ℂ) + 2 * m + 1) + 1 + ε + 2 * m = 0 := by ring
    rw [hz]
    ring
  · exact regularizedSeq_succ_of_lt ε hm
      (genericSeq_denom_at_pole_ne_zero ε (by omega))

theorem genericSeq_numer_at_pole_ne_zero {ε : ℤ} (hε : 0 ≤ ε) (r i : ℕ) :
    (ε : ℂ) + 2 * i + 1 - -((ε : ℂ) + 2 * r + 1) ≠ 0 := by
  intro h
  have he := congrArg Complex.re h
  simp only [Complex.sub_re, Complex.neg_re, Complex.add_re, Complex.intCast_re,
    Complex.mul_re, Complex.natCast_re, Complex.natCast_im, Complex.one_re,
    Complex.re_ofNat, Complex.im_ofNat, mul_zero, sub_zero, Complex.zero_re] at he
  have he0 : (0 : ℝ) ≤ ε := by exact_mod_cast hε
  have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  linarith

/-- For nonnegative parity representatives, the residue is nonzero at exactly
the sequence indices strictly above the removed denominator. -/
theorem regularizedSeq_at_pole_ne_zero_iff {ε : ℤ} (hε : 0 ≤ ε) (r m : ℕ) :
    regularizedSeq (-((ε : ℂ) + 2 * r + 1)) ε r m ≠ 0 ↔ r < m := by
  by_cases hm : r < m
  · simp only [regularizedSeq, hm, ↓reduceIte, iff_true]
    apply mul_ne_zero (genericSeq_numer_at_pole_ne_zero hε r r)
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    exact div_ne_zero (genericSeq_numer_at_pole_ne_zero hε r i)
      (genericSeq_denom_at_pole_ne_zero ε (Finset.mem_erase.mp hi).1)
  · rw [regularizedSeq_at_pole_eq_zero ε (by omega)]
    simp [hm]

/-- The reflection extension of the regularized scalar sequence. -/
def regularizedMultiplier (ν : ℂ) (ε : ℤ) (r : ℕ) : ℤ → ℂ :=
  extend ((-1) ^ ε.natAbs) (regularizedSeq ν ε r)

theorem regularizedMultiplier_eq_mul_genericMultiplier {ν : ℂ} (ε : ℤ) (r : ℕ)
    (hr : (ε : ℂ) + 2 * r + 1 + ν ≠ 0) (k : ℤ) :
    regularizedMultiplier ν ε r k =
      ((ε : ℂ) + 2 * r + 1 + ν) * genericMultiplier ν ε k := by
  simp only [regularizedMultiplier, genericMultiplier, extend,
    regularizedSeq_eq_mul_genericSeq ε r _ hr]
  split_ifs <;> ring

theorem analyticAt_regularizedMultiplier_at_pole (ε k : ℤ) (r : ℕ) :
    AnalyticAt ℂ (fun z => regularizedMultiplier z ε r k)
      (-((ε : ℂ) + 2 * r + 1)) := by
  unfold regularizedMultiplier extend
  split_ifs
  · exact analyticAt_regularizedSeq_at_pole ε r _
  · exact analyticAt_const.mul (analyticAt_regularizedSeq_at_pole ε r _)

theorem isSymmetric_regularizedMultiplier (ν : ℂ) {ε : ℤ}
    (hε : ε = 0 ∨ ε = 1) (r : ℕ) :
    IsSymmetric ε ((-1) ^ ε.natAbs) (regularizedMultiplier ν ε r) :=
  isSymmetric_extend hε (neg_one_pow_sq _) (Or.inr rfl)

/-- The regularized value at the pole satisfies the homogeneous rank-one
recurrence at that exceptional parameter. -/
theorem isRecurrent_regularizedMultiplier_at_pole {ε : ℤ}
    (hε : ε = 0 ∨ ε = 1) (r : ℕ) :
    IsRecurrent (-((ε : ℂ) + 2 * r + 1) + 1) ε
      (regularizedMultiplier (-((ε : ℂ) + 2 * r + 1)) ε r) :=
  isRecurrent_extend hε (neg_one_pow_sq _) (Or.inr rfl) fun m => by
    have h := regularizedSeq_at_pole_succ ε r m
    linear_combination h

theorem regularizedMultiplier_at_pole_ne_zero_iff {ε : ℤ}
    (hε : ε = 0 ∨ ε = 1) (r : ℕ) {k : ℤ} (hk : Even (k - ε)) :
    regularizedMultiplier (-((ε : ℂ) + 2 * r + 1)) ε r k ≠ 0 ↔
      ε + 2 * (r : ℤ) + 1 < |k| := by
  rw [regularizedMultiplier, extend_ne_zero_iff (pow_ne_zero _ (by norm_num)),
    regularizedSeq_at_pole_ne_zero_iff (by omega : 0 ≤ ε), Int.abs_eq_natAbs]
  obtain ⟨s, hs⟩ := hk
  omega

end Langlands.Archimedean.RealBlockMultiplier
