/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.OfObjectProperty
public import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# OfObjectProperty

Ported from the `proetale` package
(`Proetale.Mathlib.CategoryTheory.MorphismProperty.OfObjectProperty`).
-/

@[expose] public section

namespace CategoryTheory.MorphismProperty

@[simp]
lemma ofObjectProperty_top_right_iff {C : Type*} [Category* C] {X Y : C} {f : X ⟶ Y}
    {P : ObjectProperty C} :
    ofObjectProperty P ⊤ f ↔ P X :=
  ⟨fun h ↦ h.left, fun h ↦ ⟨h, trivial⟩⟩

@[simp]
lemma ofObjectProperty_top_left_iff {C : Type*} [Category* C] {X Y : C} {f : X ⟶ Y}
    {P : ObjectProperty C} :
    ofObjectProperty ⊤ P f ↔ P Y :=
  ⟨fun h ↦ h.right, fun h ↦ ⟨trivial, h⟩⟩

instance {C : Type*} [Category* C] (P Q : ObjectProperty C) :
    (ofObjectProperty P Q).IsStableUnderComposition where
  comp_mem _ _ hf hg := ⟨hf.left, hg.right⟩

end CategoryTheory.MorphismProperty
