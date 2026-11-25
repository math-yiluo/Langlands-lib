/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.EqToHom

/-!
# `eqToHom` in full subcategories

The underlying morphism of `eqToHom h` in a full subcategory is `eqToHom` of the equality of the
underlying objects.
-/

@[expose] public section

namespace CategoryTheory.ObjectProperty.FullSubcategory

variable {C : Type*} [Category C] {P : ObjectProperty C}

/-- The underlying morphism of `eqToHom` in a full subcategory is `eqToHom`. -/
lemma eqToHom_hom' {X Y : P.FullSubcategory} (h : X = Y) :
    (eqToHom h).hom = eqToHom (congrArg ObjectProperty.FullSubcategory.obj h) := by
  subst h
  rfl

end CategoryTheory.ObjectProperty.FullSubcategory
