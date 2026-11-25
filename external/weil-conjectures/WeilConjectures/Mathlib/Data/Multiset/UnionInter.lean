/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Data.Multiset.UnionInter

/-!
# Splitting a sub-multiset of a sum

A sub-multiset `s ≤ t + u` splits as `s = s ∩ t + (s - s ∩ t)` with `s ∩ t ≤ t` and
`s - s ∩ t ≤ u`.
-/

public section

namespace Multiset

variable {α : Type*} [DecidableEq α]

/-- If `s ≤ t + u`, then the part `s - s ∩ t` of `s` outside `t` is contained in `u`. -/
theorem sub_inter_le_of_le_add {s t u : Multiset α} (h : s ≤ t + u) : s - s ∩ t ≤ u := by
  refine le_iff_count.2 fun a ↦ ?_
  have h' := le_iff_count.1 h a
  rw [count_add] at h'
  rw [count_sub, count_inter]
  omega

end Multiset
