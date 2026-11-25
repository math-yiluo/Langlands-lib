/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

/-!
# Integer powers of a nonzero element over a finite sum

## Main statements

- `zpow_sum₀`: `a ^ (∑ i ∈ s, f i) = ∏ i ∈ s, a ^ f i` for `a ≠ 0` in a commutative group with
  zero.
-/

@[expose] public section

/-- A power of a nonzero element raised to an integer sum is the product of the powers. -/
theorem zpow_sum₀ {G ι : Type*} [CommGroupWithZero G] {a : G} (ha : a ≠ 0) (s : Finset ι)
    (f : ι → ℤ) : a ^ (∑ i ∈ s, f i) = ∏ i ∈ s, a ^ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.prod_insert hj, zpow_add₀ ha, ih]
