import Langlands.Representation.Archimedean.RealBlockMultiplier

/-!
# The generic multiplier without a condition on the real part

`RealBlockMultiplier` proves that `genericMultiplier ν ε` solves the recurrence for
`δ = ν + 1` and has no zeros, assuming `0 < re ν` and `ν ≠ ε + 2m + 1`. The hypothesis
`0 < re ν` is only used to see that the denominators `ε + 2i + 1 + ν` do not vanish. This
module replaces it by that condition, `ν ≠ -(ε + 2m + 1)` for all `m`, which also holds for
`re ν = 0`. `IsGenericParameter ν ε` packages both conditions: `ν` avoids `±(ε + 2m + 1)`.
Pure algebra.
-/

noncomputable section

namespace Langlands.Archimedean.RealBlockMultiplier

open Finset

/-- `ν` avoids `ε + 2m + 1` and `-(ε + 2m + 1)` for every `m : ℕ`. -/
def IsGenericParameter (ν : ℂ) (ε : ℤ) : Prop :=
  (∀ m : ℕ, ν ≠ (ε : ℂ) + 2 * m + 1) ∧ ∀ m : ℕ, ν ≠ -((ε : ℂ) + 2 * m + 1)

theorem genericSeq_denom_ne_zero_of_ne {ν : ℂ} {ε : ℤ}
    (hden : ∀ m : ℕ, ν ≠ -((ε : ℂ) + 2 * m + 1)) (i : ℕ) :
    (ε : ℂ) + 2 * i + 1 + ν ≠ 0 := by
  intro h
  exact hden i (by linear_combination h)

/-- For `0 ≤ ε` and `0 ≤ re ν` the denominators do not vanish. -/
theorem ne_neg_of_re_nonneg {ν : ℂ} (hν : 0 ≤ ν.re) {ε : ℤ} (hε : 0 ≤ ε) (m : ℕ) :
    ν ≠ -((ε : ℂ) + 2 * m + 1) := by
  intro h
  have h' := congrArg Complex.re h
  simp only [Complex.neg_re, Complex.add_re, Complex.intCast_re, Complex.mul_re,
    Complex.natCast_re, Complex.natCast_im, Complex.one_re, Complex.re_ofNat, Complex.im_ofNat,
    mul_zero, sub_zero] at h'
  have hε' : (0 : ℝ) ≤ ε := by exact_mod_cast hε
  have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  linarith

theorem genericSeq_succ_of_ne {ν : ℂ} {ε : ℤ}
    (hden : ∀ m : ℕ, ν ≠ -((ε : ℂ) + 2 * m + 1)) (m : ℕ) :
    genericSeq ν ε (m + 1) * (ν + 1 + ε + 2 * m) =
      ((ε : ℂ) + 2 * m + 2 - (ν + 1)) * genericSeq ν ε m := by
  have hd := genericSeq_denom_ne_zero_of_ne hden m
  rw [genericSeq, prod_range_succ, ← genericSeq]
  field_simp
  ring

theorem genericSeq_ne_zero_of_ne {ν : ℂ} {ε : ℤ}
    (hne : ∀ m : ℕ, ν ≠ (ε : ℂ) + 2 * m + 1)
    (hden : ∀ m : ℕ, ν ≠ -((ε : ℂ) + 2 * m + 1)) (m : ℕ) : genericSeq ν ε m ≠ 0 := by
  rw [genericSeq, prod_ne_zero_iff]
  intro i _
  exact div_ne_zero (sub_ne_zero.mpr (hne i).symm) (genericSeq_denom_ne_zero_of_ne hden i)

theorem isRecurrent_genericMultiplier_of_ne {ν : ℂ} {ε : ℤ} (hε : ε = 0 ∨ ε = 1)
    (hden : ∀ m : ℕ, ν ≠ -((ε : ℂ) + 2 * m + 1)) :
    IsRecurrent (ν + 1) ε (genericMultiplier ν ε) :=
  isRecurrent_extend hε (neg_one_pow_sq _) (Or.inr rfl) fun m => by
    have := genericSeq_succ_of_ne hden m
    linear_combination this

theorem genericMultiplier_ne_zero_of_ne {ν : ℂ} {ε : ℤ}
    (hne : ∀ m : ℕ, ν ≠ (ε : ℂ) + 2 * m + 1)
    (hden : ∀ m : ℕ, ν ≠ -((ε : ℂ) + 2 * m + 1)) (k : ℤ) : genericMultiplier ν ε k ≠ 0 :=
  (extend_ne_zero_iff (pow_ne_zero _ (by norm_num)) k).mpr (genericSeq_ne_zero_of_ne hne hden _)

/-- **Generic multiplier, no real-part condition.** For `ν ≠ ±(ε + 2m + 1)` there is a
symmetric solution of the recurrence for `δ = ν + 1` without zeros on the parity class. -/
theorem exists_generic_of_ne {ν : ℂ} {ε : ℤ} (hε : ε = 0 ∨ ε = 1)
    (hne : ∀ m : ℕ, ν ≠ (ε : ℂ) + 2 * m + 1)
    (hden : ∀ m : ℕ, ν ≠ -((ε : ℂ) + 2 * m + 1)) :
    ∃ μ : ℤ → ℂ, IsRecurrent (ν + 1) ε μ ∧ IsSymmetric ε ((-1) ^ ε.natAbs) μ ∧
      ∀ k : ℤ, Even (k - ε) → μ k ≠ 0 :=
  ⟨genericMultiplier ν ε, isRecurrent_genericMultiplier_of_ne hε hden,
    isSymmetric_genericMultiplier ν hε, fun k _ => genericMultiplier_ne_zero_of_ne hne hden k⟩

/-- For `0 ≤ ε` and `0 ≤ re ν`, the condition `ν ≠ ε + 2m + 1` alone makes `ν` generic. -/
theorem isGenericParameter_of_re_nonneg {ν : ℂ} (hν : 0 ≤ ν.re) {ε : ℤ} (hε : 0 ≤ ε)
    (hne : ∀ m : ℕ, ν ≠ (ε : ℂ) + 2 * m + 1) : IsGenericParameter ν ε :=
  ⟨hne, ne_neg_of_re_nonneg hν hε⟩

theorem IsGenericParameter.exists_generic {ν : ℂ} {ε : ℤ} (hε : ε = 0 ∨ ε = 1)
    (h : IsGenericParameter ν ε) :
    ∃ μ : ℤ → ℂ, IsRecurrent (ν + 1) ε μ ∧ IsSymmetric ε ((-1) ^ ε.natAbs) μ ∧
      ∀ k : ℤ, Even (k - ε) → μ k ≠ 0 :=
  exists_generic_of_ne hε h.1 h.2

end Langlands.Archimedean.RealBlockMultiplier
