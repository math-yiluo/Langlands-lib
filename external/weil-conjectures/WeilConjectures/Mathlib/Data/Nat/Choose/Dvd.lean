/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Data.Nat.Choose.Dvd
public import Mathlib.Tactic.LinearCombination

/-!
# Binomial coefficients `C(q - 1, j)` modulo `q`

Modulo `q`, the product `j! C(q - 1, j) = (q - 1) (q - 2) ⋯ (q - j)` is `(-1)^j j!`.
-/

public section

open scoped Nat

namespace Nat

/-- For `j ≤ p`, `j! C(p, j) ≡ (-1)^j j!` modulo `p + 1`: indeed
`j! C(p, j) = p (p - 1) ⋯ (p - j + 1)` and `p - i ≡ -(i + 1)` modulo `p + 1`. -/
theorem add_one_dvd_factorial_mul_choose_sub_neg_one_pow {p j : ℕ} (hj : j ≤ p) :
    ((p + 1 : ℕ) : ℤ) ∣ (j ! : ℤ) * ((p.choose j : ℤ) - (-1) ^ j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hjp : j < p := hj
    have h : ((p.choose (j + 1) * (j + 1) : ℕ) : ℤ) = ((p.choose j * (p - j) : ℕ) : ℤ) := by
      rw [choose_succ_right_eq]
    have key : ((j + 1)! : ℤ) * ((p.choose (j + 1) : ℤ) - (-1) ^ (j + 1)) =
        (j ! : ℤ) * ((p.choose j : ℤ) - (-1) ^ j) * ((p - j : ℕ) : ℤ) +
          (j ! : ℤ) * (-1) ^ j * ((p + 1 : ℕ) : ℤ) := by
      push_cast [factorial_succ, Nat.cast_sub hjp.le] at h ⊢
      linear_combination (j ! : ℤ) * h
    rw [key]
    exact Int.dvd_add ((ih hjp.le).mul_right _) (Int.dvd_mul_left _ _)

end Nat
