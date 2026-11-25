/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Sites.MorphismProperty

/-!
# MorphismProperty

Ported from the `proetale` package (`Proetale.Mathlib.CategoryTheory.Sites.MorphismProperty`).
-/

@[expose] public section

namespace CategoryTheory.MorphismProperty

variable {C : Type*} [Category C] {P : MorphismProperty C}

@[simp]
lemma singleton_mem_precoverage_iff {X Y : C} {f : X ⟶ Y} :
    Presieve.singleton f ∈ P.precoverage Y ↔ P f := by
  simp

instance : P.precoverage.IsStableUnderSup where
  sup_mem_coverings hR hS Y f hf := by
    obtain (h|h) := hf
    · exact hR h
    · exact hS h

end CategoryTheory.MorphismProperty
