/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.Basic

/-!
# Detecting isomorphisms by morphisms out of objects with a property

A morphism `f : X ⟶ Y` between objects satisfying an object property `P` is an isomorphism as
soon as postcomposition with `f` is bijective on morphisms out of every object satisfying `P`.
-/

@[expose] public section

namespace CategoryTheory.ObjectProperty

/-- A morphism `f : X ⟶ Y` between objects of a full subcategory `P` such that postcomposition
with `f` is a bijection `Hom(Q, X) ≃ Hom(Q, Y)` for every `Q` in `P` is an isomorphism. -/
lemma isIso_of_bijective_comp {D : Type*} [Category D] (P : ObjectProperty D) {X Y : D}
    (hX : P X) (hY : P Y) (f : X ⟶ Y)
    (h : ∀ Q, P Q → Function.Bijective fun g : Q ⟶ X ↦ g ≫ f) : IsIso f := by
  obtain ⟨g, hg⟩ := (h Y hY).2 (𝟙 Y)
  refine ⟨g, (h X hX).1 ?_, hg⟩
  simp only [Category.assoc, hg, Category.comp_id, Category.id_comp]

end CategoryTheory.ObjectProperty
