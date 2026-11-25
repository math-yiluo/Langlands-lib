/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Comma.CardinalArrow

/-!
# Cardinality of the morphisms of a category with few arrows

If `Arrow C` has cardinality `< κ`, then so does every type of morphisms `X ⟶ Y` in `C`.
-/

@[expose] public section

universe w v u

namespace CategoryTheory

lemma hasCardinalLT_hom_of_hasCardinalLT_arrow
    {C : Type u} [Category.{v} C] {κ : Cardinal.{w}} (h : HasCardinalLT (Arrow C) κ)
    (X Y : C) : HasCardinalLT (X ⟶ Y) κ :=
  h.of_injective Arrow.mk (Arrow.mk_injective X Y)

end CategoryTheory
