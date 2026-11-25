/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Whiskering

/-!
# Restricting commutation squares to full subcategories

Let `F : A ⥤ B`, `F' : A' ⥤ B'`, `T : A ⥤ A'` and `T' : B ⥤ B'` be functors preserving full
subcategories, and `e : F ⋙ T' ≅ T ⋙ F'` a commutation isomorphism. The restricted functors
(`ObjectProperty.lift`) satisfy the restricted commutation isomorphism, the preimage under the
fully faithful inclusion of `e` read through the identity comparisons
`ObjectProperty.liftCompιIso`. This file shows that its components are those of `e`
(`CategoryTheory.ObjectProperty.preimageIso_liftSquare_hom_app_hom`).
-/

@[expose] public section

namespace CategoryTheory.ObjectProperty

variable {A B A' B' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']
  {PA : ObjectProperty A} {PB : ObjectProperty B} {PA' : ObjectProperty A'}
  {PB' : ObjectProperty B'} {F : A ⥤ B} {F' : A' ⥤ B'} {T : A ⥤ A'} {T' : B ⥤ B'}
  (hF : ∀ K : PA.FullSubcategory, PB ((PA.ι ⋙ F).obj K))
  (hF' : ∀ K : PA'.FullSubcategory, PB' ((PA'.ι ⋙ F').obj K))
  (hT : ∀ K : PA.FullSubcategory, PA' ((PA.ι ⋙ T).obj K))
  (hT' : ∀ K : PB.FullSubcategory, PB' ((PB.ι ⋙ T').obj K))
  (e : F ⋙ T' ≅ T ⋙ F')

/-- The components of the restriction to full subcategories of a commutation isomorphism
`e : F ⋙ T' ≅ T ⋙ F'` are those of `e`. -/
lemma preimageIso_liftSquare_hom_app_hom (K : PA.FullSubcategory) :
    ((((PB'.fullyFaithfulι).whiskeringRight _).preimageIso
      (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (PB.lift (PA.ι ⋙ F) hF) (PB'.liftCompιIso (PB.ι ⋙ T') hT') ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (PB.liftCompιIso (PA.ι ⋙ F) hF) T' ≪≫
        Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft PA.ι e ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (PA'.liftCompιIso (PA.ι ⋙ T) hT).symm F' ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (PA'.lift (PA.ι ⋙ T) hT) (PB'.liftCompιIso (PA'.ι ⋙ F') hF').symm ≪≫
        (Functor.associator _ _ _).symm)).hom.app K).hom = e.hom.app K.obj := by
  simp [liftCompιIso]

/-- The components of the inverse of the restriction to full subcategories of a commutation
isomorphism `e : F ⋙ T' ≅ T ⋙ F'` are those of the inverse of `e`. -/
lemma preimageIso_liftSquare_inv_app_hom (K : PA.FullSubcategory) :
    ((((PB'.fullyFaithfulι).whiskeringRight _).preimageIso
      (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (PB.lift (PA.ι ⋙ F) hF) (PB'.liftCompιIso (PB.ι ⋙ T') hT') ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (PB.liftCompιIso (PA.ι ⋙ F) hF) T' ≪≫
        Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft PA.ι e ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (PA'.liftCompιIso (PA.ι ⋙ T) hT).symm F' ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (PA'.lift (PA.ι ⋙ T) hT) (PB'.liftCompιIso (PA'.ι ⋙ F') hF').symm ≪≫
        (Functor.associator _ _ _).symm)).inv.app K).hom = e.inv.app K.obj := by
  simp [liftCompιIso]

end CategoryTheory.ObjectProperty
