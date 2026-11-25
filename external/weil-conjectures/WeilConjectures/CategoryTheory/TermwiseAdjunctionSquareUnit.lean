/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Adjunction.Whiskering

/-! # Termwise normalization of an adjunction square

Source: Stacks Project, Modules on Sites, Tag 03DI; termwise adjunction calculation.
(blueprint: lem-cbc-termwise-adjunction-square-unit). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

open CategoryTheory CategoryTheory.Functor

namespace CategoryTheory

/-- The square isomorphism induced by right whiskering.
Source: Stacks Project, Tag 03DI; termwise functor construction.
(blueprint: lem-cbc-termwise-adjunction-square-unit). -/
def termwiseAdjunctionIso {I A B C D : Type*}
    [Category I] [Category A] [Category B] [Category C] [Category D]
    {F : A ⥤ B} {G : B ⥤ D} {H : A ⥤ C} {K : C ⥤ D}
    (e : F ⋙ G ≅ H ⋙ K) :
    (whiskeringRight I _ _).obj F ⋙ (whiskeringRight I _ _).obj G ≅
      (whiskeringRight I _ _).obj H ⋙ (whiskeringRight I _ _).obj K :=
  whiskeringRightObjCompIso F G ≪≫ (whiskeringRight I _ _).mapIso e ≪≫
    (whiskeringRightObjCompIso H K).symm

/-- A normalized transpose equation is preserved by passage to functor categories.

Apply extensionality of natural transformations. At each indexing object, the
whiskered adjunction unit and the mapped natural isomorphism evaluate to the original
unit and isomorphism component. The resulting equation is exactly the assumed one,
written using the unit formula for the adjunction bijection.

Source: Stacks Project, Modules on Sites, Tag 03DI; componentwise adjunction calculation.
(blueprint: lem-cbc-termwise-adjunction-square-unit). -/
theorem termwiseAdjunctionSquareUnit {I A B C D : Type*}
    [Category I] [Category A] [Category B] [Category C] [Category D]
    {J : A ⥤ B} {P : B ⥤ A} {J' : C ⥤ D} {P' : D ⥤ C}
    (a : J ⊣ P) (a' : J' ⊣ P') (F : A ⥤ C) (G : B ⥤ D)
    (e : J ⋙ G ≅ F ⋙ J') (z : G ⋙ P' ≅ P ⋙ F)
    (h : ∀ M, a'.homEquiv _ _ (e.inv.app M) =
      F.map (a.unit.app M) ≫ z.inv.app (J.obj M)) (M : I ⥤ A) :
    (a'.whiskerRight I).homEquiv _ _ ((termwiseAdjunctionIso e).inv.app M) =
      ((whiskeringRight I _ _).obj F).map ((a.whiskerRight I).unit.app M) ≫
        (termwiseAdjunctionIso z).inv.app
          (((whiskeringRight I _ _).obj J).obj M) := by
  rw [Adjunction.homEquiv_unit]
  apply NatTrans.ext
  funext n
  have hh := h (M.obj n)
  rw [Adjunction.homEquiv_unit] at hh
  simp only [termwiseAdjunctionIso, Iso.trans_inv, NatTrans.comp_app, Functor.mapIso_inv,
    whiskeringRight, whiskeringRightObjCompIso, Iso.refl_hom, Iso.refl_inv,
    Iso.symm_inv, NatTrans.id_app, Functor.comp_obj,
    whiskerRight_app, Adjunction.whiskerRight_unit_app_app,
    Category.id_comp, Category.comp_id, Functor.map_comp]
  erw [P'.map_id, Category.comp_id]
  exact hh


end CategoryTheory
