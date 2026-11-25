/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory

/-!
# Monoidal functors between functor categories

The functor category `C ⥤ E` is monoidal (resp. braided, symmetric) whenever `E` is, with all
the structure defined pointwise. Precomposition with a functor `F : C ⥤ D` is strong monoidal
by `CategoryTheory.Functor.Monoidal.whiskeringLeft`; here we record that it is moreover braided.
The constant functor `E ⥤ (C ⥤ E)` is monoidal (`CategoryTheory.Functor.Monoidal.const`).
-/

@[expose] public section

namespace CategoryTheory

variable {C D : Type*} [Category* C] [Category* D]

/-- Precomposition with a functor `F : C ⥤ D` is a braided functor `(D ⥤ E) ⥤ (C ⥤ E)`. -/
instance Functor.Braided.whiskeringLeft (E : Type*) [Category* E] [MonoidalCategory E]
    [BraidedCategory E] (F : C ⥤ D) : ((whiskeringLeft _ _ E).obj F).Braided where
  braided X Y := by
    ext c
    exact (Category.id_comp _).trans (Category.comp_id _).symm

/-- The constant functor `A ⥤ (C ⥤ A)` is monoidal, the tensor product of functors being
computed pointwise. -/
instance Functor.Monoidal.const (C : Type*) [Category* C] (A : Type*) [Category* A]
    [MonoidalCategory A] : (Functor.const C : A ⥤ C ⥤ A).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := NatIso.ofComponents fun _ ↦ Iso.refl _
      μIso _ _ := NatIso.ofComponents fun _ ↦ Iso.refl _ }

end CategoryTheory
