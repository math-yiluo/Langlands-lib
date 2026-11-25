/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.CofilteredSystem
import Mathlib.CategoryTheory.Limits.Types.Images

/-!
# Nonempty limit of a Mittag-Leffler tower of sets

Source: Stacks Project, Algebra, Lemma 0597, with Definition 0595 and Example 0596
(blueprint: lem-weil-pbc-ml-sets-tower-limit-nonempty).
-/

@[expose] public section

universe u

open CategoryTheory

namespace CategoryTheory.Functor

/-- A tower of nonempty sets satisfying the Mittag-Leffler condition has a nonempty limit
(Stacks Project, Algebra, Lemma 0597, with Definition 0595 and Example 0596).
The tower `(E_i, f_i)_{i ≥ 1}` (def-weil-inverse-system) is a functor `F : ℕᵒᵖ ⥤ Type u`,
the index `n : ℕ` denoting the positive index `n + 1`, so that `F.map` of `m ≥ n` is the
composite `φ_{m+1,n+1}`; the Mittag-Leffler condition is Mathlib's
`Functor.IsMittagLeffler` (for `ℕᵒᵖ` it says: for every `i` some `c ≥ i` has
`Im(E_c → E_i) ⊆ Im(E_k → E_i)` for all `k ≥ i`, i.e. `Im(E_k → E_i) = Im(E_c → E_i)` for
all `k ≥ c`), and the limit is the set `F.sections` of compatible families.

Proof (following the node):
1. Put `B_i = φ_{c(i),i}(E_{c(i)})`, nonempty since `E_{c(i)}` is. The images
`φ_{k,i}(E_k)` decrease in `k` because `φ_{k,i} = φ_{j,i} ∘ φ_{k,j}`, and equal `B_i` for
`k ≥ c(i)`; so `B_i` is the intersection of all of them.
2. `f_i` maps `B_{i+1}` onto `B_i`: for `k ≥ max(c(i), c(i+1), i+1)` write elements of
`B_{i+1}` and `B_i` as images of `E_k` and use stabilization at `i` and `i+1`. Hence
`(B_i)` is a tower of nonempty sets with surjective transitions, and its compatible
sequences are those of `(E_i)` (a compatible `(e_i)` has `e_i = φ_{k,i}(e_k) ∈ B_i`).
3. Choose `b_1 ∈ B_1` and successive preimages `b_{i+1} ∈ B_{i+1}` of `b_i` by dependent
choice; the sequence is compatible, so lies in the limit of `(E_i)`.
(blueprint: lem-weil-pbc-ml-sets-tower-limit-nonempty) -/
theorem nonempty_sections_of_isMittagLeffler (F : ℕᵒᵖ ⥤ Type u)
    [∀ n : ℕᵒᵖ, Nonempty (F.obj n)] (hF : F.IsMittagLeffler) :
    F.sections.Nonempty := by
  let G := F.toEventualRanges
  have hsurj : ∀ n, Function.Surjective
      (G.map (CategoryTheory.homOfLE (Nat.le_succ n)).op) := by
    intro n
    exact F.surjective_toEventualRanges hF _
  have hproj : Function.Surjective
      ((CategoryTheory.Limits.Types.limitCone G).π.app ⟨0⟩) :=
    CategoryTheory.Limits.Types.surjective_π_app_zero_of_surjective_map
      (CategoryTheory.Limits.Types.limitConeIsLimit G) hsurj
  obtain ⟨x, hx⟩ := hproj (Classical.choice (F.toEventualRanges_nonempty hF ⟨0⟩))
  let y := (F.toEventualRangesSectionsEquiv) x
  exact ⟨y, y.property⟩

end CategoryTheory.Functor
