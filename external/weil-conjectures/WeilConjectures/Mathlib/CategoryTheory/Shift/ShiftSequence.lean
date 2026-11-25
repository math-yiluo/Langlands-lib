/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Shift.ShiftSequence
public import Mathlib.CategoryTheory.Shift.ShiftedHom

/-!
# Shift sequences and composition of shifted morphisms

For a functor `F` with a shift sequence, the morphism induced by a composite
`ShiftedHom.comp f g` is the composite of the morphisms induced by `f` and `g`
(`CategoryTheory.Functor.shiftMap_shiftedHomComp`).
-/

@[expose] public section

namespace CategoryTheory.Functor

variable {C A : Type*} [Category C] [Category A] {M : Type*} [AddMonoid M] [HasShift C M]
  (F : C ⥤ A) [F.ShiftSequence M]

/-- The morphism `(F.shift a).obj X ⟶ (F.shift a'').obj Z` induced by the composite of shifted
morphisms `f : X ⟶ Y⟦m⟧` and `g : Y ⟶ Z⟦n⟧` is the composite of the induced morphisms. -/
lemma shiftMap_shiftedHomComp {X Y Z : C} {m n mn : M} (f : X ⟶ Y⟦m⟧) (g : Y ⟶ Z⟦n⟧)
    (h : n + m = mn) (a a' a'' : M) (ha' : m + a = a') (ha'' : n + a' = a'') :
    F.shiftMap (ShiftedHom.comp f g h) a a'' (by rw [← h, ← ha'', ← ha', add_assoc]) =
      F.shiftMap f a a' ha' ≫ F.shiftMap g a' a'' ha'' := by
  rw [shiftMap, ShiftedHom.comp, Functor.map_comp, Functor.map_comp, Category.assoc,
    Category.assoc, shiftMap, Category.assoc, F.shiftIso_hom_app_comp_shiftMap g m mn h]

end CategoryTheory.Functor
