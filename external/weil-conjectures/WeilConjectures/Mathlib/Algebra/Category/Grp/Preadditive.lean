/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Grp.Preadditive
public import Mathlib.Algebra.BigOperators.Finsupp.Basic

/-!
# Finite sums of morphisms of abelian groups

A finite sum of morphisms in `AddCommGrpCat` is computed pointwise.
-/

@[expose] public section

open CategoryTheory

/-- A finite sum of morphisms of abelian groups is computed pointwise. -/
lemma AddCommGrpCat.sum_apply {M N : AddCommGrpCat} {ι : Type*} (f : ι → (M ⟶ N))
    (s : Finset ι) (x : M) : (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x := by
  rw [← AddMonoidHom.finsetSum_apply]
  exact congr($(map_sum AddCommGrpCat.homAddEquiv f s) x)
