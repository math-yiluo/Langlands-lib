/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.NumberTheory.Basic
public import Mathlib.Algebra.Polynomial.AlgebraMap

/-!

# Powers of `1 + ℓ x`

In any ring, `(1 + ℓ x) ^ (ℓ ^ m) - 1` is divisible by `ℓ ^ (m + 1)`
(`exists_one_add_natCast_mul_pow_sub_one_eq`, from `dvd_sub_pow_of_dvd_sub` in `ℤ[X]`). In
particular `1 + ℓ x` has order dividing `ℓ ^ m` when `ℓ ^ m = 0` (`one_add_natCast_mul_pow_eq_one`).

-/

@[expose] public section

/-- In any ring, `(1 + ℓ x) ^ (ℓ ^ m) - 1` is divisible by `ℓ ^ (m + 1)`. -/
theorem exists_one_add_natCast_mul_pow_sub_one_eq {R : Type*} [Ring R] (ℓ m : ℕ) (x : R) :
    ∃ y : R, (1 + ℓ * x) ^ (ℓ ^ m) - 1 = (ℓ : R) ^ (m + 1) * y := by
  obtain ⟨q, hq⟩ := dvd_sub_pow_of_dvd_sub (R := Polynomial ℤ) (p := ℓ)
    (a := 1 + (ℓ : Polynomial ℤ) * Polynomial.X) (b := 1) ⟨Polynomial.X, by ring⟩ m
  have := congrArg (Polynomial.aeval x) hq
  simp only [one_pow, map_sub, map_pow, map_add, map_one, map_mul, map_natCast,
    Polynomial.aeval_X] at this
  exact ⟨_, this⟩

/-- In a ring in which `ℓ ^ m = 0`, the element `1 + ℓ x` has order dividing `ℓ ^ m`. -/
theorem one_add_natCast_mul_pow_eq_one {R : Type*} [Ring R] {ℓ m : ℕ} (h : (ℓ : R) ^ m = 0)
    (x : R) : (1 + ℓ * x) ^ (ℓ ^ m) = 1 := by
  obtain ⟨y, hy⟩ := exists_one_add_natCast_mul_pow_sub_one_eq ℓ m x
  rw [← sub_eq_zero, hy, pow_succ', mul_assoc, h, zero_mul, mul_zero]
