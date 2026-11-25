/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Subobject.Lattice
public import WeilConjectures.CategoryTheory.Abelian.Filtration

/-!
# Blueprint statements

lem-sp-finite-filtration-induction.
-/

@[expose] public section

universe v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- lem-sp-finite-filtration-induction. -/
structure WeilFilteredObject (C : Type u) [Category.{v} C] [Abelian C] where
  obj : C
  filtration : DecreasingFiltration obj

namespace WeilFilteredObject

/-- lem-sp-finite-filtration-induction. -/
structure Hom (A B : WeilFilteredObject C) where
  hom : A.obj ⟶ B.obj
  preserves : ∀ i : ℤ, ∃ lift : (A.filtration.F i : C) ⟶
    (B.filtration.F i : C),
    lift ≫ (B.filtration.F i).arrow = (A.filtration.F i).arrow ≫ hom

end WeilFilteredObject

namespace DecreasingFiltration

/-- lem-sp-finite-filtration-induction. -/
def IsFinite {A : C} (F : DecreasingFiltration A) : Prop :=
  ∃ n m : ℤ, F.F n = ⊤ ∧ F.F m = ⊥

end DecreasingFiltration

end CategoryTheory
