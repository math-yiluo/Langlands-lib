/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.Retract
public import WeilConjectures.FromJoel.CategoryTheory.Idempotents.Basic

/-!
# Full subcategories closed under retracts are idempotent complete

Supplement to `Mathlib.CategoryTheory.ObjectProperty.Retract`, migrated from
the branch `jriou_localization` of Joël Riou's mathlib fork
(leanprover-community/mathlib4#25848), adapted to mathlib `v4.33.1`.

-/

@[expose] public section

universe v u

namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C] (P : ObjectProperty C)

instance [IsIdempotentComplete C] [P.IsStableUnderRetracts] :
    IsIdempotentComplete P.FullSubcategory where
  idempotents_split := by
    rintro X p hp
    obtain ⟨Y, e, he⟩ := retract_of_isIdempotentComplete X.1 p.hom
      ((ObjectProperty.ι _).congr_map hp)
    exact ⟨⟨Y, P.prop_of_retract e X.2⟩, homMk e.i, homMk e.r,
      by cat_disch, by cat_disch⟩

end CategoryTheory.ObjectProperty
