/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic

/-!
# Basic

Ported from the `proetale` package (`Proetale.Mathlib.CategoryTheory.Comma.StructuredArrow.Basic`).
-/

@[expose] public section

namespace CategoryTheory

@[simps! obj_left obj_hom map_left]
def CostructuredArrow.lift {J C D : Type*} [Category* J] [Category* C] [Category* D]
    (F : J ⥤ C)
    {L : C ⥤ D} {X : D} (s : F ⋙ L ⟶ (Functor.const _).obj X) :
    J ⥤ CostructuredArrow L X where
  obj j := .mk (s.app j)
  map {i j} f := CostructuredArrow.homMk (F.map f)
    (by
      simp only [mk_left, ← Functor.comp_map, mk_hom_eq_self, NatTrans.naturality,
        Functor.const_obj_map]
      exact Category.comp_id _)

@[simp]
lemma CostructuredArrow.lift_forget {J C D : Type*} [Category* J] [Category* C] [Category* D]
    (F : J ⥤ C) {L : C ⥤ D} {X : D} (s : F ⋙ L ⟶ (Functor.const _).obj X) :
    lift F s ⋙ CategoryTheory.CostructuredArrow.proj _ _ = F :=
  rfl

end CategoryTheory
