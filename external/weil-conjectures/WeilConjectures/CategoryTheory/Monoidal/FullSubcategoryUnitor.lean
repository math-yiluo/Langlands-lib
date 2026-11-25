/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Subcategory

/-!
# Underlying morphisms of the unitors in a full monoidal subcategory

The underlying morphism of the right unitor of an object `X` of a full monoidal subcategory is the
right unitor of `X.obj`. These are `rfl`-lemmas; rewriting with them, rather than leaving the
identification to definitional unfolding, keeps the kernel from unfolding the monoidal structure
of the full subcategory when comparing large morphisms.
-/

@[expose] public section

namespace CategoryTheory.ObjectProperty

open MonoidalCategory

variable {C : Type*} [Category* C] [MonoidalCategory C] (P : ObjectProperty C) [P.IsMonoidal]

/-- The underlying morphism of the right unitor in a full monoidal subcategory. -/
lemma rightUnitor_hom_hom (X : P.FullSubcategory) : (ρ_ X).hom.hom = (ρ_ X.obj).hom :=
  rfl

/-- The underlying morphism of the inverse right unitor in a full monoidal subcategory. -/
lemma rightUnitor_inv_hom (X : P.FullSubcategory) : (ρ_ X).inv.hom = (ρ_ X.obj).inv :=
  rfl

end CategoryTheory.ObjectProperty
