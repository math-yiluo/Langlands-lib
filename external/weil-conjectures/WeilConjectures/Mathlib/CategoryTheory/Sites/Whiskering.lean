/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.CategoryTheory.Equivalence

/-!
# Adjunctions between categories of sheaves induced by adjunctions of coefficients

- `CategoryTheory.sheafCompose_additive`: composing sheaves with an additive functor is additive.
- `CategoryTheory.sheafComposeAdjunction`: an adjunction `F ⊣ G` between coefficient
  categories, both of which preserve sheaves, induces an adjunction
  `sheafCompose J F ⊣ sheafCompose J G`, whose unit and counit are obtained by whiskering.
-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C) {A : Type u₂}
  [Category.{v₂} A] {B : Type u₃} [Category.{v₃} B] {F : A ⥤ B} {G : B ⥤ A}
  (adj : F ⊣ G) [J.HasSheafCompose F] [J.HasSheafCompose G]

/-- An adjunction `F ⊣ G` between coefficient categories, both of which preserve sheaves,
induces an adjunction `sheafCompose J F ⊣ sheafCompose J G` between categories of sheaves,
whose unit and counit are obtained by whiskering. -/
noncomputable def sheafComposeAdjunction : sheafCompose J F ⊣ sheafCompose J G :=
  Adjunction.mkOfUnitCounit
    { unit :=
        { app P := ObjectProperty.homMk (Functor.whiskerLeft P.obj adj.unit)
          naturality P Q φ := by ext1; ext U; exact adj.unit.naturality _ }
      counit :=
        { app P := ObjectProperty.homMk (Functor.whiskerLeft P.obj adj.counit)
          naturality P Q φ := by ext1; ext U; exact adj.counit.naturality _ }
      left_triangle := by
        ext P : 2; ext1; ext U
        simp only [Functor.comp_obj, Functor.id_obj, NatTrans.comp_app, Functor.whiskerRight_app,
          Functor.associator_hom_app, Functor.whiskerLeft_app, Category.id_comp,
          ObjectProperty.FullSubcategory.comp_hom, sheafCompose_map_hom,
          NatTrans.id_app', ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app]
        exact adj.left_triangle_components _
      right_triangle := by
        ext P : 2; ext1; ext U
        simp only [Functor.comp_obj, Functor.id_obj, NatTrans.comp_app, Functor.whiskerLeft_app,
          Functor.associator_inv_app, Functor.whiskerRight_app, Category.id_comp,
          ObjectProperty.FullSubcategory.comp_hom, sheafCompose_map_hom,
          NatTrans.id_app', ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app]
        exact adj.right_triangle_components _ }

@[simp]
lemma sheafComposeAdjunction_unit_app_hom (P : Sheaf J A) :
    ((sheafComposeAdjunction J adj).unit.app P).hom = Functor.whiskerLeft P.obj adj.unit :=
  rfl

@[simp]
lemma sheafComposeAdjunction_counit_app_hom (P : Sheaf J B) :
    ((sheafComposeAdjunction J adj).counit.app P).hom = Functor.whiskerLeft P.obj adj.counit :=
  rfl

section Additive

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C) {A : Type u₂}
  [Category.{v₂} A] [Preadditive A] {B : Type u₃} [Category.{v₃} B] [Preadditive B]
  (F : A ⥤ B) [F.Additive] [J.HasSheafCompose F]

/-- Composing sheaves with an additive functor is additive. -/
instance sheafCompose_additive : (sheafCompose J F).Additive where
  map_add {_ _ _ _} := by
    ext : 3
    exact F.map_add

end Additive

/-- Composing sheaves with an equivalence of coefficient categories is an equivalence. -/
lemma isEquivalence_sheafCompose_of_isEquivalence {C A B : Type*} [Category C] [Category A]
    [Category B] (J : GrothendieckTopology C) (E : A ⥤ B) [E.IsEquivalence]
    [J.HasSheafCompose E] [J.HasSheafCompose E.inv] :
    (sheafCompose J E).IsEquivalence :=
  ((E.adjunction.whiskerRight Cᵒᵖ).restrictFullyFaithful
    (fullyFaithfulSheafToPresheaf J A) (fullyFaithfulSheafToPresheaf J B)
    (L := sheafCompose J E) (R := sheafCompose J E.inv)
    (Iso.refl _) (Iso.refl _)).toEquivalence.isEquivalence_functor

end CategoryTheory
