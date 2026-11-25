/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Whiskering

/-! # Termwise lifting of a transformation between composite functors

Source: Mathlib CategoryTheory/Whiskering; the termwise refinement of Stacks Tag 0F7B.
(blueprint: def-cbc-termwise-composite-transformation)
-/

@[expose] public section

set_option autoImplicit false

namespace CategoryTheory.Functor

/-- Lift a transformation between two composites to diagrams, retaining the four factors.
Source: Mathlib `Functor.whiskeringRightObjCompIso`; Stacks Tag 0F7B refinement.
(blueprint: def-cbc-termwise-composite-transformation). -/
@[irreducible] def termwiseCompositeTransformation
    (I A B C D : Type*) [Category I] [Category A] [Category B] [Category C] [Category D]
    (f : A ⥤ B) (g : B ⥤ D) (h : A ⥤ C) (k : C ⥤ D) (t : f ⋙ g ⟶ h ⋙ k) :
    (whiskeringRight I A B).obj f ⋙ (whiskeringRight I B D).obj g ⟶
      (whiskeringRight I A C).obj h ⋙ (whiskeringRight I C D).obj k :=
  (whiskeringRightObjCompIso f g).hom ≫ (whiskeringRight I A D).map t ≫
    (whiskeringRightObjCompIso h k).inv

end CategoryTheory.Functor
