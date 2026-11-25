/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Data.Finset.Order
public import Mathlib.Data.Finset.Sort
public import WeilConjectures.Mathlib.Order.Directed

/-!
# Selected upper bounds of finite sets in a directed preorder

Let `α` be a preorder, `i₀ : α` a base point and `d : α → α → α` a selection of pairwise upper
bounds, i.e. `a ≤ d a b` and `b ≤ d a b`. For a finite set `F` we define the upper bound
`Finset.directedBound i₀ d F` by inserting the elements of `F` one at a time,
`u(∅) = i₀` and `u(F ∪ {i}) = d (u F) i`. Since `d` need not be commutative or associative,
the insertion order matters; we use the order of `Finset.toList`.

## Main definitions and results

- `Finset.directedBound`: the selected upper bound.
- `Finset.le_directedBound`: every element of `F` lies below `Finset.directedBound i₀ d F`.
-/

@[expose] public section

variable {α : Type*}

namespace Finset

/-- Blueprint `theorem-nagata-s-compactification-theorem--1`: Selected upper bound of a finite set.

Given a base point `i₀` and selected pairwise upper bounds `d`, the upper bound `u F` of a
finite set `F` is defined by insertion: `u ∅ = i₀` and `u (F ∪ {i}) = d (u F) i`, the elements
of `F` being inserted in the order of `Finset.toList`. -/
noncomputable def directedBound (i₀ : α) (d : α → α → α) (F : Finset α) : α :=
  F.toList.directedBound i₀ d

@[simp]
lemma directedBound_empty (i₀ : α) (d : α → α → α) : directedBound i₀ d ∅ = i₀ := by
  simp [directedBound]

variable [Preorder α] {i₀ : α} {d : α → α → α}

/-- Blueprint `theorem-nagata-s-compactification-theorem--1`: Property of the selected finite upper
bound. Every element of `F` lies below the selected upper bound `u F`. -/
lemma le_directedBound (hd : ∀ a b, a ≤ d a b ∧ b ≤ d a b) {F : Finset α} {i : α}
    (hi : i ∈ F) : i ≤ directedBound i₀ d F :=
  List.le_directedBound hd (Finset.mem_toList.mpr hi)

/-- The base point lies below the selected upper bound. -/
lemma base_le_directedBound (hd : ∀ a b, a ≤ d a b ∧ b ≤ d a b) (F : Finset α) :
    i₀ ≤ directedBound i₀ d F :=
  List.base_le_directedBound hd _

end Finset
