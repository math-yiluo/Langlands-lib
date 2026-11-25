/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.SubcategoryShift

/-!
# Monoidal natural transformations of a full monoidal subcategory commute with the shifts

Let `P` be a full monoidal subcategory of a monoidal category `C` with a shift, stable under the
shift, such that the functors `K ⊗ -` and `- ⊗ K` of `C` commute with the shifts. Then so do
those of `P` (`ObjectProperty.commShiftTensorLeft`). This file shows that the following natural
transformations of `P` commute with the shifts as soon as their analogues in `C` do:

* `g ⊗ -` and `- ⊗ g` for a morphism `g` of `P` (`ObjectProperty.commShift_curriedTensor_map`,
  `ObjectProperty.commShift_curriedTensor_flip_map`);
* the associator `(- ⊗ Y) ⊗ Z ≅ - ⊗ (Y ⊗ Z)`, natural in its first variable
  (`ObjectProperty.commShift_associatorNatTrans₁`);
* the left unitor `𝟙 ⊗ - ≅ -` (`ObjectProperty.commShift_leftUnitorNatTrans`).

All of them are proved by the same argument: through the fully faithful inclusion `P.ι`, which
commutes with the shifts, the natural transformation of `P` is the one of `C`, conjugated by the
isomorphisms `ObjectProperty.tensorLeftCompιIso` and `ObjectProperty.tensorRightCompιIso`
(`NatTrans.CommShift.of_whiskerRight`).
-/

@[expose] public section

namespace CategoryTheory

open MonoidalCategory

namespace NatTrans.CommShift

variable {C D E : Type*} [Category* C] [Category* D] [Category* E] {A : Type*} [AddMonoid A]
  [HasShift C A] [HasShift D A] [HasShift E A]

/-- A natural transformation `τ : F₁ ⟶ F₂` commutes with the shifts if, after composition with a
faithful functor `G` commuting with the shifts, it is the conjugate of a natural transformation
commuting with the shifts by isomorphisms commuting with the shifts. -/
lemma of_whiskerRight_eq {F₁ F₂ : C ⥤ D} (τ : F₁ ⟶ F₂) [F₁.CommShift A] [F₂.CommShift A]
    (G : D ⥤ E) [G.CommShift A] [G.Faithful] {H₁ H₂ : C ⥤ E} [H₁.CommShift A] [H₂.CommShift A]
    (e₁ : F₁ ⋙ G ≅ H₁) (e₂ : F₂ ⋙ G ≅ H₂) (σ : H₁ ⟶ H₂) [NatTrans.CommShift e₁.hom A]
    [NatTrans.CommShift e₂.hom A] [NatTrans.CommShift σ A]
    (h : Functor.whiskerRight τ G = e₁.hom ≫ σ ≫ e₂.inv) : NatTrans.CommShift τ A := by
  have : NatTrans.CommShift (Functor.whiskerRight τ G) A := by
    rw [h]
    infer_instance
  exact of_whiskerRight τ G

end NatTrans.CommShift

namespace ObjectProperty

variable {C : Type*} [Category* C] [MonoidalCategory C] (P : ObjectProperty C) [P.IsMonoidal]
  {A : Type*} [AddMonoid A] [HasShift C A] [P.IsStableUnderShift A]
  [∀ X : C, ((curriedTensor C).obj X).CommShift A]
  [∀ X : C, ((curriedTensor C).flip.obj X).CommShift A]

omit [∀ X : C, ((curriedTensor C).flip.obj X).CommShift A] in
/-- The natural transformation `g ⊗ - : X ⊗ - ⟶ X' ⊗ -` of `P` commutes with the shifts if that
of `C` does. -/
lemma commShift_curriedTensor_map {X X' : P.FullSubcategory} (g : X ⟶ X')
    [NatTrans.CommShift ((curriedTensor C).map g.hom) A] :
    NatTrans.CommShift ((curriedTensor P.FullSubcategory).map g) A := by
  have : P.ι.Faithful := P.faithful_ι
  refine NatTrans.CommShift.of_whiskerRight_eq _ P.ι (P.tensorLeftCompιIso X)
    (P.tensorLeftCompιIso X') (Functor.whiskerLeft P.ι ((curriedTensor C).map g.hom)) ?_
  ext Y
  simp only [Functor.whiskerRight_app, NatTrans.comp_app, Functor.whiskerLeft_app,
    tensorLeftCompιIso, tensorLeftIsoLift, liftFullSubcategoryCompιIso, Iso.trans_hom,
    Iso.trans_inv, Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv, Iso.symm_hom,
    Iso.symm_inv, NatIso.ofComponents_inv_app, NatIso.ofComponents_hom_app, Iso.refl_inv,
    Iso.refl_hom]
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp,
    Category.id_comp, Category.comp_id, Category.comp_id]
  rfl

omit [∀ X : C, ((curriedTensor C).obj X).CommShift A] in
/-- The natural transformation `- ⊗ g : - ⊗ X ⟶ - ⊗ X'` of `P` commutes with the shifts if that
of `C` does. -/
lemma commShift_curriedTensor_flip_map {X X' : P.FullSubcategory} (g : X ⟶ X')
    [NatTrans.CommShift ((curriedTensor C).flip.map g.hom) A] :
    NatTrans.CommShift ((curriedTensor P.FullSubcategory).flip.map g) A := by
  have : P.ι.Faithful := P.faithful_ι
  refine NatTrans.CommShift.of_whiskerRight_eq _ P.ι (P.tensorRightCompιIso X)
    (P.tensorRightCompιIso X') (Functor.whiskerLeft P.ι ((curriedTensor C).flip.map g.hom)) ?_
  ext Y
  simp only [Functor.whiskerRight_app, NatTrans.comp_app, Functor.whiskerLeft_app,
    tensorRightCompιIso, tensorRightIsoLift, liftFullSubcategoryCompιIso, Iso.trans_hom,
    Iso.trans_inv, Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv, Iso.symm_hom,
    Iso.symm_inv, NatIso.ofComponents_inv_app, NatIso.ofComponents_hom_app, Iso.refl_inv,
    Iso.refl_hom]
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp,
    Category.id_comp, Category.comp_id, Category.comp_id]
  rfl

omit [∀ X : C, ((curriedTensor C).obj X).CommShift A] in
set_option synthInstance.maxSize 4096 in
-- the instance problems for the composite functors are large
/-- The associator `(- ⊗ Y) ⊗ Z ≅ - ⊗ (Y ⊗ Z)` of `P`, natural in its first variable, commutes
with the shifts if that of `C` does. -/
lemma commShift_associatorNatTrans₁ (Y Z : P.FullSubcategory)
    [NatTrans.CommShift (associatorNatTrans₁ C Y.obj Z.obj) A] :
    NatTrans.CommShift (associatorNatTrans₁ P.FullSubcategory Y Z) A := by
  have : P.ι.Faithful := P.faithful_ι
  let eF : ((curriedTensor P.FullSubcategory).flip.obj Y ⋙ (curriedTensor _).flip.obj Z) ⋙ P.ι ≅
      P.ι ⋙ ((curriedTensor C).flip.obj Y.obj ⋙ (curriedTensor C).flip.obj Z.obj) :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (P.tensorRightCompιIso Z) ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (P.tensorRightCompιIso Y) _ ≪≫
      Functor.associator _ _ _
  have : NatTrans.CommShift eF.hom A := by
    dsimp only [eF, Iso.trans_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Iso.symm_hom]
    infer_instance
  refine NatTrans.CommShift.of_whiskerRight_eq _ P.ι eF (P.tensorRightCompιIso (Y ⊗ Z))
    (Functor.whiskerLeft P.ι (associatorNatTrans₁ C Y.obj Z.obj)) ?_
  ext X
  simp only [Functor.comp_obj, Functor.flip_obj_obj, curriedTensor_obj_obj, ι_obj,
    tensorObj_obj, Functor.whiskerRight_app, associatorNatTrans₁_app, associator_def,
    isoMk_hom, ι_map, homMk_hom, tensorRightCompιIso, tensorRightIsoLift,
    liftFullSubcategoryCompιIso, Iso.trans_refl, Functor.isoWhiskerRight_twice,
    Iso.trans_assoc, Iso.trans_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Iso.symm_hom, Iso.symm_inv, Functor.isoWhiskerRight_inv, Category.assoc,
    NatTrans.comp_app, Functor.associator_hom_app, Functor.whiskerLeft_app,
    NatIso.ofComponents_inv_app, Iso.refl_inv, FullSubcategory.id_hom, Functor.comp_map,
    Functor.flip_obj_map, curriedTensor_map_app, Functor.associator_inv_app,
    NatIso.ofComponents_hom_app, Iso.refl_hom, Category.id_comp, eF]
  erw [MonoidalCategory.id_whiskerRight, Category.id_comp, Category.comp_id]
  exact (Category.id_comp _).symm

end ObjectProperty

namespace MonoidalCategory

variable (C : Type*) [Category* C] [MonoidalCategory C]

/-- The left unitor `𝟙 ⊗ X ≅ X`, as a natural transformation `𝟙 ⊗ - ⟶ 𝟭`. -/
@[simps]
def leftUnitorNatTrans : (curriedTensor C).obj (𝟙_ C) ⟶ 𝟭 C where
  app X := (λ_ X).hom

end MonoidalCategory

namespace ObjectProperty

variable {C : Type*} [Category* C] [MonoidalCategory C] (P : ObjectProperty C) [P.IsMonoidal]
  {A : Type*} [AddMonoid A] [HasShift C A] [P.IsStableUnderShift A]
  [∀ X : C, ((curriedTensor C).obj X).CommShift A]

/-- The left unitor `𝟙 ⊗ - ⟶ 𝟭` of `P` commutes with the shifts if that of `C` does. -/
lemma commShift_leftUnitorNatTrans [NatTrans.CommShift (leftUnitorNatTrans C) A] :
    NatTrans.CommShift (leftUnitorNatTrans P.FullSubcategory) A := by
  have : P.ι.Faithful := P.faithful_ι
  have : NatTrans.CommShift (Functor.leftUnitor P.ι ≪≫ (Functor.rightUnitor P.ι).symm).hom A := by
    dsimp only [Iso.trans_hom, Iso.symm_hom]
    infer_instance
  refine NatTrans.CommShift.of_whiskerRight_eq _ P.ι (P.tensorLeftCompιIso (𝟙_ _))
    (Functor.leftUnitor _ ≪≫ (Functor.rightUnitor _).symm)
    (Functor.whiskerLeft P.ι (leftUnitorNatTrans C)) ?_
  ext X
  simp only [Functor.whiskerRight_app, NatTrans.comp_app, Functor.whiskerLeft_app,
    tensorLeftCompιIso, tensorLeftIsoLift, liftFullSubcategoryCompιIso, Iso.trans_hom,
    Iso.trans_inv, Functor.isoWhiskerRight_hom, Iso.symm_hom,
    Iso.symm_inv, NatIso.ofComponents_inv_app, Iso.refl_inv,
    Iso.refl_hom, leftUnitorNatTrans_app, Functor.leftUnitor_inv_app,
    Functor.rightUnitor_hom_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id, Category.comp_id]
  erw [NatTrans.id_app, Category.id_comp]
  rfl

end ObjectProperty

end CategoryTheory
