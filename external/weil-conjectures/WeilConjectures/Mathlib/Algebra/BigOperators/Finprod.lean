/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Group.Units.Equiv

/-!
# Shifting the index of a finite sum over `ℤ`

If `c : ℤ → M` and its shift `i ↦ c (i + 1)` both vanish outside a finite set `s`, then
`∑ i ∈ s, c (i + 1) = ∑ i ∈ s, c i` (`Finset.sum_comp_add_one_eq_sum`): both sums are the
`finsum` of `c`.
-/

@[expose] public section

namespace Finset

/-- If `c` and `i ↦ c (i + 1)` both vanish outside the finite set `s ⊆ ℤ`, then the sums over
`s` of `c` and of its shift agree. -/
theorem sum_comp_add_one_eq_sum {M : Type*} [AddCommMonoid M] (s : Finset ℤ) (c : ℤ → M)
    (h₁ : ∀ i ∉ s, c i = 0) (h₂ : ∀ i ∉ s, c (i + 1) = 0) :
    ∑ i ∈ s, c (i + 1) = ∑ i ∈ s, c i := by
  rw [← finsum_eq_sum_of_support_subset (fun i ↦ c (i + 1))
      fun i hi ↦ by_contra fun h ↦ hi (h₂ i h),
    ← finsum_eq_sum_of_support_subset c fun i hi ↦ by_contra fun h ↦ hi (h₁ i h)]
  exact finsum_comp_equiv (Equiv.addRight 1)

end Finset
