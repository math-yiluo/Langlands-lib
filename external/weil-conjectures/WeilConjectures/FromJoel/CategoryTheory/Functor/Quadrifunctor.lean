/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Functor.Trifunctor
public import Mathlib.CategoryTheory.Functor.CurryingThree
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Functor.Quadrifunctor

/-!
# Quatrifunctors

Migrated from `Mathlib/CategoryTheory/Functor/Quadrifunctor.lean`
on the branch `jriou_localization` of Joël Riou's mathlib fork
(leanprover-community/mathlib4#25848), adapted to mathlib `v4.33.1`.

-/

@[expose] public section

namespace CategoryTheory

open _root_.CategoryTheory.Functor

variable {C₁ C₂ C₃ C₄ C₁₂₃ C₂₃₄ C D₁ D₂ D₃ D₄ E : Type*}
  [Category C₁] [Category C₂] [Category C₃] [Category C₁₂₃]
  [Category C₄] [Category C₂₃₄] [Category C]
  [Category D₁] [Category D₂] [Category D₃] [Category D₄] [Category E]

@[simps!]
def trifunctorComp₁₂₃ (F₁₂₃ : C₁ ⥤ C₂ ⥤ C₃ ⥤ C₁₂₃) (G : C₁₂₃ ⥤ C₄ ⥤ C) :
    C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ C :=
  (Functor.postcompose₃.obj G).obj F₁₂₃

variable (E)

/-- Auxiliary definition for `whiskeringLeft₄`. -/
@[simps!]
def whiskeringLeft₄ObjObjObjObj (F₁ : C₁ ⥤ D₁) (F₂ : C₂ ⥤ D₂) (F₃ : C₃ ⥤ D₃) (F₄ : C₄ ⥤ D₄) :
    (D₁ ⥤ D₂ ⥤ D₃ ⥤ D₄ ⥤ E) ⥤ C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ E :=
  (whiskeringRight _ _ _).obj ((((whiskeringLeft₃ E).obj F₂).obj F₃).obj F₄) ⋙
    (whiskeringLeft C₁ D₁ _).obj F₁

set_option backward.defeqAttrib.useBackward true in
/-- Auxiliary definition for `whiskeringLeft₄`. -/
@[simps]
def whiskeringLeft₄ObjObjObjMap (F₁ : C₁ ⥤ D₁) (F₂ : C₂ ⥤ D₂) (F₃ : C₃ ⥤ D₃)
    {F₄ F₄' : C₄ ⥤ D₄} (τ₄ : F₄ ⟶ F₄') :
    whiskeringLeft₄ObjObjObjObj E F₁ F₂ F₃ F₄ ⟶
      whiskeringLeft₄ObjObjObjObj E F₁ F₂ F₃ F₄' where
  app F := whiskerLeft _ (whiskerLeft _ ((((whiskeringLeft₃ E).obj F₂).obj F₃).map τ₄))

variable (C₄ D₄) in
/-- Auxiliary definition for `whiskeringLeft₄`. -/
@[simps]
def whiskeringLeft₄ObjObjObj (F₁ : C₁ ⥤ D₁) (F₂ : C₂ ⥤ D₂) (F₃ : C₃ ⥤ D₃) :
    (C₄ ⥤ D₄) ⥤ (D₁ ⥤ D₂ ⥤ D₃ ⥤ D₄ ⥤ E) ⥤ (C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ E) where
  obj F₄ := whiskeringLeft₄ObjObjObjObj E F₁ F₂ F₃ F₄
  map τ₄ := whiskeringLeft₄ObjObjObjMap E F₁ F₂ F₃ τ₄

set_option backward.defeqAttrib.useBackward true in
variable (C₄ D₄) in
/-- Auxiliary definition for `whiskeringLeft₃`. -/
@[simps]
def whiskeringLeft₄ObjObjMap (F₁ : C₁ ⥤ D₁) (F₂ : C₂ ⥤ D₂) {F₃ F₃' : C₃ ⥤ D₃} (τ₃ : F₃ ⟶ F₃') :
    whiskeringLeft₄ObjObjObj C₄ D₄ E F₁ F₂ F₃ ⟶ whiskeringLeft₄ObjObjObj C₄ D₄ E F₁ F₂ F₃' where
  app F₄ := whiskerRight ((whiskeringRight _ _ _).map
    ((((whiskeringLeft₃ E).obj F₂).map τ₃).app F₄)) _

variable (C₃ C₄ D₃ D₄) in
/-- Auxiliary definition for `whiskeringLeft₄`. -/
@[simps]
def whiskeringLeft₄ObjObj (F₁ : C₁ ⥤ D₁) (F₂ : C₂ ⥤ D₂) :
    (C₃ ⥤ D₃) ⥤ (C₄ ⥤ D₄) ⥤ (D₁ ⥤ D₂ ⥤ D₃ ⥤ D₄ ⥤ E) ⥤ (C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ E) where
  obj F₃ := whiskeringLeft₄ObjObjObj C₄ D₄ E F₁ F₂ F₃
  map τ₃ := whiskeringLeft₄ObjObjMap C₄ D₄ E F₁ F₂ τ₃

set_option backward.defeqAttrib.useBackward true in
variable (C₃ C₄ D₃ D₄) in
/-- Auxiliary definition for `whiskeringLeft₃`. -/
@[simps]
def whiskeringLeft₄ObjMap (F₁ : C₁ ⥤ D₁) {F₂ F₂' : C₂ ⥤ D₂} (τ₂ : F₂ ⟶ F₂') :
    whiskeringLeft₄ObjObj C₃ C₄ D₃ D₄ E F₁ F₂ ⟶ whiskeringLeft₄ObjObj C₃ C₄ D₃ D₄ E F₁ F₂' where
  app F₃ :=
    { app F₄ := whiskerRight ((whiskeringRight _ _ _).map
        ((((whiskeringLeft₃ E).map τ₂).app F₃).app F₄)) _ }
  naturality F₃ F₃' τ₃ := by
    ext F₄ G X₁ X₂ X₃ X₄
    exact congr_app (((G.obj (F₁.obj X₁)).map (τ₂.app X₂)).naturality (τ₃.app X₃)) (F₄.obj X₄)

variable (C₂ C₃ C₄ D₂ D₃ D₄) in
/-- Auxiliary definition for `whiskeringLeft₄`. -/
@[simps]
def whiskeringLeft₄Obj (F₁ : C₁ ⥤ D₁) :
    (C₂ ⥤ D₂) ⥤ (C₃ ⥤ D₃) ⥤ (C₄ ⥤ D₄) ⥤ (D₁ ⥤ D₂ ⥤ D₃ ⥤ D₄ ⥤ E) ⥤ (C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ E) where
  obj F₂ := whiskeringLeft₄ObjObj C₃ C₄ D₃ D₄ E F₁ F₂
  map τ₂ := whiskeringLeft₄ObjMap C₃ C₄ D₃ D₄ E F₁ τ₂

set_option backward.defeqAttrib.useBackward true in
variable (C₂ C₃ C₄ D₂ D₃ D₄) in
/-- Auxiliary definition for `whiskeringLeft₄`. -/
@[simps]
def whiskeringLeft₄Map {F₁ F₁' : C₁ ⥤ D₁} (τ₁ : F₁ ⟶ F₁') :
    whiskeringLeft₄Obj C₂ C₃ C₄ D₂ D₃ D₄ E F₁ ⟶ whiskeringLeft₄Obj C₂ C₃ C₄ D₂ D₃ D₄ E F₁' where
  app F₂ :=
    { app F₃ :=
      { app F₄ := whiskerLeft _ ((whiskeringLeft _ _ _).map τ₁)
        naturality _ _ _ := by
          ext
          dsimp
          simp only [NatTrans.naturality] }
      naturality F₃ F₃' τ₃ := by
        ext F₄ G X₁ X₂ X₃ X₄
        dsimp
        simp only [← NatTrans.comp_app, NatTrans.naturality] }
  naturality F₂ F₂' τ₂ := by
    ext F₃ F₄ G X₁ X₂ X₃ X₄
    dsimp
    simp only [← NatTrans.comp_app, NatTrans.naturality]

/-- The obvious functor
`(C₁ ⥤ D₁) ⥤ (C₂ ⥤ D₂) ⥤ (C₃ ⥤ D₃) ⥤ (C₄ ⥤ D₄) ⥤ (D₁ ⥤ D₂ ⥤ D₃ ⥤ D₄ ⥤ E) ⥤ (C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ E)`.
-/
@[simps!]
def whiskeringLeft₄ :
    (C₁ ⥤ D₁) ⥤ (C₂ ⥤ D₂) ⥤ (C₃ ⥤ D₃) ⥤ (C₄ ⥤ D₄) ⥤
    (D₁ ⥤ D₂ ⥤ D₃ ⥤ D₄ ⥤ E) ⥤ (C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ E) where
  obj F₁ := whiskeringLeft₄Obj C₂ C₃ C₄ D₂ D₃ D₄ E F₁
  map τ₁ := whiskeringLeft₄Map C₂ C₃ C₄ D₂ D₃ D₄ E τ₁

variable {E}

/-- The equivalence of categories `(C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ E) ≌ C₁ × C₂ × C₃ × C₄ ⥤ E`
given by the curryfication of functors in four variables. -/
def currying₄ : (C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ E) ≌ (C₁ × C₂ × C₃ × C₄ ⥤ E) :=
  currying.trans (currying₃.trans ((prod.associativity C₁ C₂ (C₃ × C₄)).congrLeft))

/-- Uncurrying a functor in four variables. -/
abbrev uncurry₄ : (C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ E) ⥤ C₁ × C₂ × C₃ × C₄ ⥤ E := currying₄.functor

/-- Currying a functor in four variables. -/
abbrev curry₄ : (C₁ × C₂ × C₃ × C₄ ⥤ E) ⥤ C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ E := currying₄.inverse

/-- Uncurrying functors in four variables gives a fully faithful functor. -/
def fullyFaithfulUncurry₄ :
    (uncurry₄ : (C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ E) ⥤ (C₁ × C₂ × C₃ × C₄ ⥤ E)).FullyFaithful :=
  currying₄.fullyFaithfulFunctor

@[simp]
lemma curry₄_obj_map_app_app_app (F : C₁ × C₂ × C₃ × C₄ ⥤ E)
    {X₁ Y₁ : C₁} (f : X₁ ⟶ Y₁) (X₂ : C₂) (X₃ : C₃) (X₄ : C₄) :
    ((((curry₄.obj F).map f).app X₂).app X₃).app X₄ = F.map ⟨f, 𝟙 X₂, 𝟙 X₃, 𝟙 X₄⟩ := rfl

@[simp]
lemma curry₄_obj_obj_map_app_app (F : C₁ × C₂ × C₃ × C₄ ⥤ E)
    (X₁ : C₁) {X₂ Y₂ : C₂} (f : X₂ ⟶ Y₂) (X₃ : C₃) (X₄ : C₄) :
    ((((curry₄.obj F).obj X₁).map f).app X₃).app X₄ = F.map ⟨𝟙 X₁, f, 𝟙 X₃, 𝟙 X₄⟩ := rfl

@[simp]
lemma curry₄_obj_obj_obj_map_app (F : C₁ × C₂ × C₃ × C₄ ⥤ E)
    (X₁ : C₁) (X₂ : C₂) {X₃ Y₃ : C₃} (f : X₃ ⟶ Y₃) (X₄ : C₄) :
    ((((curry₄.obj F).obj X₁).obj X₂).map f).app X₄ = F.map ⟨𝟙 X₁, 𝟙 X₂, f, 𝟙 X₄⟩ := rfl

@[simp]
lemma curry₄_obj_obj_obj_obj_map (F : C₁ × C₂ × C₃ × C₄ ⥤ E)
    (X₁ : C₁) (X₂ : C₂) (X₃ : C₃) {X₄ Y₄ : C₄} (f : X₄ ⟶ Y₄) :
    ((((curry₄.obj F).obj X₁).obj X₂).obj X₃).map f = F.map ⟨𝟙 X₁, 𝟙 X₂, 𝟙 X₃, f⟩ := rfl

@[simp]
lemma curry₄_map_app_app_app_app {F G : C₁ × C₂ × C₃ × C₄ ⥤ E} (f : F ⟶ G)
    (X₁ : C₁) (X₂ : C₂) (X₃ : C₃) (X₄ : C₄) :
    ((((curry₄.map f).app X₁).app X₂).app X₃).app X₄ = f.app ⟨X₁, X₂, X₃, X₄⟩ := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma currying₄_unitIso_hom_app_app_app_app_app (F : C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ E)
    (X₁ : C₁) (X₂ : C₂) (X₃ : C₃) (X₄ : C₄) :
    ((((currying₄.unitIso.hom.app F).app X₁).app X₂).app X₃).app X₄ = 𝟙 _ := by
  simp only [id_obj, currying₄, Equivalence.trans_functor, Equivalence.congrLeft_functor,
    prod.associativity_inverse, Equivalence.trans_inverse, Equivalence.congrLeft_inverse,
    prod.associativity_functor, comp_obj, whiskeringLeft_obj_obj, currying_inverse_obj_obj_obj,
    Equivalence.trans_unitIso, isoWhiskerRight_trans, Iso.trans_assoc, isoWhiskerLeft_trans,
    Iso.trans_hom, isoWhiskerRight_hom, Iso.symm_hom, isoWhiskerLeft_hom, NatTrans.comp_app,
    whiskerRight_app, rightUnitor_inv_app, map_id, whiskerLeft_app,
    Equivalence.congrLeft_unitIso_hom_app, associator_inv_app, associator_hom_app,
    Category.comp_id, Category.id_comp, currying_functor_obj_obj, currying_unitIso_hom_app_app_app,
    currying_inverse_map_app_app, currying₃_unitIso_hom_app_app_app_app, curry₃_map_app_app_app,
    Equivalence.funInvIdAssoc_inv_app, prod.associator_obj, prod.inverseAssociator_obj,
    Equivalence.unit, prod.associativity_unitIso, Iso.refl_hom, NatTrans.id_app, prod_id]
  exact Functor.map_id _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma currying₄_unitIso_inv_app_app_app_app_app (F : C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ E)
    (X₁ : C₁) (X₂ : C₂) (X₃ : C₃) (X₄ : C₄) :
    ((((currying₄.unitIso.inv.app F).app X₁).app X₂).app X₃).app X₄ = 𝟙 _ := by
  simp only [currying₄, Equivalence.trans_functor, Equivalence.congrLeft_functor,
    prod.associativity_inverse, Equivalence.trans_inverse, Equivalence.congrLeft_inverse,
    prod.associativity_functor, comp_obj, whiskeringLeft_obj_obj, currying_inverse_obj_obj_obj,
    id_obj, Equivalence.trans_unitIso, isoWhiskerRight_trans, Iso.trans_assoc,
    isoWhiskerLeft_trans, Iso.trans_inv, isoWhiskerRight_inv, Iso.symm_inv, isoWhiskerLeft_inv,
    Category.assoc, NatTrans.comp_app, associator_inv_app, whiskerRight_app, associator_hom_app,
    map_id, whiskerLeft_app, Equivalence.congrLeft_unitIso_inv_app, rightUnitor_hom_app,
    Category.id_comp, currying_inverse_map_app_app, currying_functor_obj_obj,
    currying_unitIso_inv_app_app_app, Category.comp_id, curry₃_map_app_app_app,
    Equivalence.funInvIdAssoc_hom_app, prod.associator_obj, prod.inverseAssociator_obj,
    Equivalence.unitInv, prod.associativity_unitIso, Iso.refl_inv, NatTrans.id_app, prod_id,
    currying₃_unitIso_inv_app_app_app_app]
  exact Functor.map_id _ _

@[simp]
lemma uncurry₄_obj_map (F : C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ E) {X Y : C₁ × C₂ × C₃ × C₄} (f : X ⟶ Y) :
    (uncurry₄.obj F).map f =
      (((((F.map f.1).app X.2.1).app X.2.2.1).app X.2.2.2 ≫
        (((F.obj Y.1).map f.2.1).app X.2.2.1).app X.2.2.2) ≫
          (((F.obj Y.1).obj Y.2.1).map f.2.2.1).app X.2.2.2) ≫
          (((F.obj Y.1).obj Y.2.1).obj Y.2.2.1).map f.2.2.2 := by
  rfl

@[simp]
lemma uncurry₄_map_app {F G : C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ E} (f : F ⟶ G) (X : C₁ × C₂ × C₃ × C₄) :
    (uncurry₄.map f).app X = (((f.app X.1).app X.2.1).app X.2.2.1).app X.2.2.2 := by
  rfl

end CategoryTheory
