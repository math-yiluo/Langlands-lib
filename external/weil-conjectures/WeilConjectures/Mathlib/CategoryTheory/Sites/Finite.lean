/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Sites.Finite

/-!
# Finite

Ported from the `proetale` package (`Proetale.Mathlib.CategoryTheory.Sites.Finite`).
-/

@[expose] public section

namespace CategoryTheory

variable {C : Type*} [Category C]

instance : (Precoverage.finite C).IsStableUnderSup where
  sup_mem_coverings hR hS := hR.union hS

def Precoverage.singleton (C : Type*) [Category* C] : Precoverage C where
  coverings X R := ∃ (Y : C) (f : Y ⟶ X), R = .singleton f

@[simp, grind .]
lemma Precoverage.singleton_mem_singleton {X Y : C} (f : Y ⟶ X) :
    Presieve.singleton f ∈ Precoverage.singleton C X :=
  ⟨_, _, rfl⟩

theorem Precoverage.singleton_le_finite (C : Type*) [Category* C] :
    Precoverage.singleton C ≤ Precoverage.finite _ :=
  fun X R ⟨Y, f, hf⟩ ↦ by subst hf; simp

end CategoryTheory
