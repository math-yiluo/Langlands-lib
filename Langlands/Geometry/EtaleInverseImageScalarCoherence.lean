import Langlands.Geometry.EtaleInverseImageScalars
import Langlands.Geometry.EtaleInverseImageCoherence

/-! # Geometric coherence of the actual scalar-extension comparison -/

noncomputable section

universe u

namespace Langlands.Geometry.EtaleInverseImage

open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
open EtaleDirectImage EtaleCohomologyAction

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

private theorem conjugate_scalarUniqueness
    {C D : Type*} [Category* C] [Category* D]
    {L L' : C ⥤ D} {G G' : D ⥤ C}
    (a : L ⊣ G) (b : L' ⊣ G') (e : G ≅ G') :
    conjugateEquiv b a ((a.ofNatIsoRight e).leftAdjointUniq b).hom = e.inv := by
  ext Y
  apply ((a.homEquiv _ _).symm).injective
  simp only [Adjunction.homEquiv_counit]
  rw [conjugateEquiv_counit]
  exact Adjunction.leftAdjointUniq_hom_app_counit (a.ofNatIsoRight e) b Y

private theorem conjugate_associator_inv
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : B ⥤ C} {R₂ : C ⥤ B}
    {L₃ : C ⥤ D} {R₃ : D ⥤ C}
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) (c : L₃ ⊣ R₃) :
    conjugateEquiv ((a.comp b).comp c) (a.comp (b.comp c))
        (associator L₁ L₂ L₃).inv =
      (associator R₃ R₂ R₁).inv := by
  have h : conjugateIsoEquiv (a.comp (b.comp c)) ((a.comp b).comp c)
      (associator L₁ L₂ L₃) = associator R₃ R₂ R₁ := by
    apply Iso.ext
    exact conjugateEquiv_associator_hom a b c
  exact congrArg Iso.inv h

variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
variable {X Z V : Scheme.{u}}

/-- The constructed scalar comparison is conjugate to the inverse of the
strict geometric direct-image/scalar-restriction interchange. -/
theorem conjugate_inverseImageExtendScalarsIso (f : Z ⟶ X) :
    conjugateEquiv
        ((inverseImageAdjunction f R).comp (sheafExtendRestrictScalarsAdj φ Z))
        ((sheafExtendRestrictScalarsAdj φ X).comp (inverseImageAdjunction f S))
        (inverseImageExtendScalarsIso φ f).hom =
      (directImageRestrictScalarsIso φ f).inv :=
  conjugate_scalarUniqueness _ _ _

/-- Coefficient extension commutes with the actual identity inverse-image
comparison, retaining both functor unitors. -/
theorem inverseImageExtendScalarsIso_id (X : Scheme.{u}) :
    (inverseImageExtendScalarsIso φ (𝟙 X)).hom ≫
        whiskerRight (inverseImageId R X).hom (sheafExtendScalars φ X) ≫
        (sheafExtendScalars φ X).leftUnitor.hom =
      whiskerLeft (sheafExtendScalars φ X) (inverseImageId S X).hom ≫
        (sheafExtendScalars φ X).rightUnitor.hom := by
  apply (conjugateEquiv (sheafExtendRestrictScalarsAdj φ X)
    ((sheafExtendRestrictScalarsAdj φ X).comp
      (inverseImageAdjunction (𝟙 X) S))).injective
  rw [← conjugateEquiv_comp _
      ((inverseImageAdjunction (𝟙 X) R).comp (sheafExtendRestrictScalarsAdj φ X)),
    ← conjugateEquiv_comp _ (Adjunction.id.comp (sheafExtendRestrictScalarsAdj φ X)),
    ← conjugateEquiv_comp _ ((sheafExtendRestrictScalarsAdj φ X).comp Adjunction.id)]
  simp only [conjugate_inverseImageExtendScalarsIso, conjugateEquiv_whiskerRight,
    conjugateEquiv_whiskerLeft, conjugate_inverseImageId,
    conjugateEquiv_leftUnitor_hom, conjugateEquiv_rightUnitor_hom]
  apply NatTrans.ext
  funext F
  dsimp [directImageRestrictScalarsIso]
  simp only [Category.id_comp]
  apply Sheaf.hom_ext
  rfl

/-- The two orders of scalar interchange and geometric composition agree
as actual natural transformations, including the functor associators. -/
theorem inverseImageExtendScalarsIso_comp (f : Z ⟶ X) (g : V ⟶ Z) :
    whiskerRight (inverseImageExtendScalarsIso φ f).hom (inverseImage g S) ≫
        (associator (inverseImage f R) (sheafExtendScalars φ Z) (inverseImage g S)).hom ≫
        whiskerLeft (inverseImage f R) (inverseImageExtendScalarsIso φ g).hom ≫
        (associator (inverseImage f R) (inverseImage g R)
          (sheafExtendScalars φ V)).inv ≫
        whiskerRight (inverseImageComp R f g).hom (sheafExtendScalars φ V) =
      (associator (sheafExtendScalars φ X) (inverseImage f S) (inverseImage g S)).hom ≫
        whiskerLeft (sheafExtendScalars φ X) (inverseImageComp S f g).hom ≫
        (inverseImageExtendScalarsIso φ (g ≫ f)).hom := by
  apply (conjugateEquiv
    ((inverseImageAdjunction (g ≫ f) R).comp (sheafExtendRestrictScalarsAdj φ V))
    (((sheafExtendRestrictScalarsAdj φ X).comp (inverseImageAdjunction f S)).comp
      (inverseImageAdjunction g S))).injective
  rw [← conjugateEquiv_comp _
      (((inverseImageAdjunction f R).comp (sheafExtendRestrictScalarsAdj φ Z)).comp
        (inverseImageAdjunction g S)),
    ← conjugateEquiv_comp _
      ((inverseImageAdjunction f R).comp
        ((sheafExtendRestrictScalarsAdj φ Z).comp (inverseImageAdjunction g S))),
    ← conjugateEquiv_comp _
      ((inverseImageAdjunction f R).comp
        ((inverseImageAdjunction g R).comp (sheafExtendRestrictScalarsAdj φ V))),
    ← conjugateEquiv_comp _
      (((inverseImageAdjunction f R).comp (inverseImageAdjunction g R)).comp
        (sheafExtendRestrictScalarsAdj φ V)),
    ← conjugateEquiv_comp _
      ((sheafExtendRestrictScalarsAdj φ X).comp
        ((inverseImageAdjunction f S).comp (inverseImageAdjunction g S))),
    ← conjugateEquiv_comp _
      ((sheafExtendRestrictScalarsAdj φ X).comp (inverseImageAdjunction (g ≫ f) S))]
  simp only [conjugate_inverseImageExtendScalarsIso, conjugate_inverseImageComp,
    conjugateEquiv_whiskerLeft, conjugateEquiv_whiskerRight,
    conjugateEquiv_associator_hom, conjugate_associator_inv]
  apply NatTrans.ext
  funext F
  dsimp [directImageRestrictScalarsIso]
  simp only [Category.comp_id]
  apply Sheaf.hom_ext
  rfl

/-- The actual two-step scalar comparison, with geometric-composition
coherence recorded by the equality below. -/
def inverseImageExtendScalarsTwoStepIso (f : Z ⟶ X) (g : V ⟶ Z) :
    (sheafExtendScalars φ X ⋙ inverseImage f S) ⋙ inverseImage g S ≅
      inverseImage (g ≫ f) R ⋙ sheafExtendScalars φ V :=
  isoWhiskerRight (inverseImageExtendScalarsIso φ f) (inverseImage g S) ≪≫
    associator (inverseImage f R) (sheafExtendScalars φ Z) (inverseImage g S) ≪≫
    isoWhiskerLeft (inverseImage f R) (inverseImageExtendScalarsIso φ g) ≪≫
    (associator (inverseImage f R) (inverseImage g R) (sheafExtendScalars φ V)).symm ≪≫
    isoWhiskerRight (inverseImageComp R f g) (sheafExtendScalars φ V)

theorem inverseImageExtendScalarsTwoStepIso_eq (f : Z ⟶ X) (g : V ⟶ Z) :
    inverseImageExtendScalarsTwoStepIso φ f g =
      associator (sheafExtendScalars φ X) (inverseImage f S) (inverseImage g S) ≪≫
        isoWhiskerLeft (sheafExtendScalars φ X) (inverseImageComp S f g) ≪≫
        inverseImageExtendScalarsIso φ (g ≫ f) := by
  apply Iso.ext
  simpa only [inverseImageExtendScalarsTwoStepIso, Iso.trans_hom, Iso.symm_hom,
    isoWhiskerLeft_hom, isoWhiskerRight_hom] using inverseImageExtendScalarsIso_comp φ f g

end Langlands.Geometry.EtaleInverseImage
