/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.MateOfNatIsoLeft

/-!
# Invertibility of mates of pasted invertible squares

The horizontal composite `CategoryTheory.Functor.isoHComp` of two invertible 2-squares; its mate
is an isomorphism as soon as both mates are (`CategoryTheory.isIso_mateEquiv_isoHComp`), by
`CategoryTheory.isIso_mateEquiv_hComp`.
-/

@[expose] public section

namespace CategoryTheory

open TwoSquare

variable {A B C D E F : Type*} [Category A] [Category B] [Category C] [Category D]
  [Category E] [Category F]

section IsoHComp

variable {T : A ⥤ C} {T' : C ⥤ E} {L : A ⥤ B} {R : C ⥤ D} {R' : E ⥤ F} {B₁ : B ⥤ D}
  {B₂ : D ⥤ F}

/-- The horizontal composite of two invertible 2-squares `e₁ : T ⋙ R ≅ L ⋙ B₁` and
`e₂ : T' ⋙ R' ≅ R ⋙ B₂`, as an isomorphism `(T ⋙ T') ⋙ R' ≅ L ⋙ (B₁ ⋙ B₂)`; its underlying
2-square is `e₁.hom ≫ₕ e₂.hom` (`CategoryTheory.Functor.isoHComp_hom`). -/
noncomputable def _root_.CategoryTheory.Functor.isoHComp (e₁ : T ⋙ R ≅ L ⋙ B₁)
    (e₂ : T' ⋙ R' ≅ R ⋙ B₂) : (T ⋙ T') ⋙ R' ≅ L ⋙ (B₁ ⋙ B₂) :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft T e₂ ≪≫ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight e₁ B₂ ≪≫ Functor.associator _ _ _

/-- The underlying 2-square of `CategoryTheory.Functor.isoHComp e₁ e₂` is `e₁.hom ≫ₕ e₂.hom`. -/
lemma _root_.CategoryTheory.Functor.isoHComp_hom (e₁ : T ⋙ R ≅ L ⋙ B₁)
    (e₂ : T' ⋙ R' ≅ R ⋙ B₂) :
    (Functor.isoHComp e₁ e₂).hom = (e₁.hom ≫ₕ e₂.hom : TwoSquare _ _ _ _) :=
  rfl


/-- The components of `CategoryTheory.Functor.isoHComp e₁ e₂`. -/
@[simp]
lemma _root_.CategoryTheory.Functor.isoHComp_hom_app (e₁ : T ⋙ R ≅ L ⋙ B₁)
    (e₂ : T' ⋙ R' ≅ R ⋙ B₂) (X : A) :
    (Functor.isoHComp e₁ e₂).hom.app X = e₂.hom.app (T.obj X) ≫ B₂.map (e₁.hom.app X) := by
  simp [Functor.isoHComp]

/-- The mate of the horizontal composite `CategoryTheory.Functor.isoHComp e₁ e₂` of two invertible
2-squares is an isomorphism if the mates of `e₁` and `e₂` are. -/
lemma isIso_mateEquiv_isoHComp {R₂ : D ⥤ C} {R₃ : F ⥤ E}
    {R₁ : B ⥤ A} (adj₁ : L ⊣ R₁) (adj₂ : R ⊣ R₂) (adj₃ : R' ⊣ R₃)
    (e₁ : T ⋙ R ≅ L ⋙ B₁) (e₂ : T' ⋙ R' ≅ R ⋙ B₂)
    [IsIso (mateEquiv adj₁ adj₂ e₁.hom)] [IsIso (mateEquiv adj₂ adj₃ e₂.hom)] :
    IsIso (mateEquiv adj₁ adj₃ (Functor.isoHComp e₁ e₂).hom) :=
  isIso_mateEquiv_hComp adj₁ adj₂ adj₃ e₁.hom e₂.hom

end IsoHComp

end CategoryTheory
