/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Order.Directed

/-!
# Selected upper bounds of finite lists in a directed preorder

Let `α` be a preorder, `i₀ : α` a base point and `d : α → α → α` a selection of pairwise upper
bounds, i.e. `a ≤ d a b` and `b ≤ d a b`. For a list `l` we define the upper bound
`List.directedBound i₀ d l` by inserting the elements of `l` one at a time, starting from `i₀`.
The version for finite sets is `Finset.directedBound`
(`WeilConjectures.Mathlib.Data.Finset.Order`).

## Main definitions and results

- `List.directedBound`: the selected upper bound.
- `List.le_directedBound`: every element of `l` lies below `List.directedBound i₀ d l`.
-/

@[expose] public section

variable {α : Type*}

namespace List

/-- The upper bound of the elements of a list obtained by successively inserting its elements,
starting from the base point `i₀`, using the selected pairwise upper bounds `d`. -/
def directedBound (i₀ : α) (d : α → α → α) (l : List α) : α :=
  l.foldr (fun i b ↦ d b i) i₀

@[simp]
lemma directedBound_nil (i₀ : α) (d : α → α → α) : directedBound i₀ d [] = i₀ := rfl

@[simp]
lemma directedBound_cons (i₀ : α) (d : α → α → α) (i : α) (l : List α) :
    directedBound i₀ d (i :: l) = d (directedBound i₀ d l) i := rfl

variable [Preorder α] {i₀ : α} {d : α → α → α}

lemma base_le_directedBound (hd : ∀ a b, a ≤ d a b ∧ b ≤ d a b) (l : List α) :
    i₀ ≤ directedBound i₀ d l := by
  induction l with
  | nil => exact le_rfl
  | cons i l ih => exact ih.trans (hd _ _).1

lemma le_directedBound (hd : ∀ a b, a ≤ d a b ∧ b ≤ d a b) {l : List α} {i : α} (hi : i ∈ l) :
    i ≤ directedBound i₀ d l := by
  induction l with
  | nil => simp at hi
  | cons j l ih =>
    rcases List.mem_cons.mp hi with rfl | hi
    · exact (hd _ _).2
    · exact (ih hi).trans (hd _ _).1

end List
