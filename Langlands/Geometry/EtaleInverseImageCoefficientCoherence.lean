import Langlands.Geometry.EtaleInverseImageScalarCoherence
import Langlands.Geometry.EtaleScalarExtensionCoherence

/-! # Coefficient-ring coherence of arbitrary inverse-image scalar extension -/

noncomputable section

universe u

namespace Langlands.Geometry.EtaleInverseImage

open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
open EtaleDirectImage EtaleCohomologyAction

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

private theorem conjugate_coefficient_associator_inv
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

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
variable {X Z : Scheme.{u}} (f : Z ⟶ X)

/-- The scalar comparison for the identity coefficient homomorphism agrees
with the actual coefficient-identity isomorphisms and functor unitors. -/
theorem inverseImageExtendScalarsIso_ringId :
    (inverseImageExtendScalarsIso (RingHom.id R) f).hom ≫
        whiskerLeft (inverseImage f R) (sheafExtendScalarsIdIso Z).hom ≫
        (inverseImage f R).rightUnitor.hom =
      whiskerRight (sheafExtendScalarsIdIso X).hom (inverseImage f R) ≫
        (inverseImage f R).leftUnitor.hom := by
  apply (conjugateEquiv (inverseImageAdjunction f R)
    ((sheafExtendRestrictScalarsAdj (RingHom.id R) X).comp
      (inverseImageAdjunction f R))).injective
  rw [← conjugateEquiv_comp _
      ((inverseImageAdjunction f R).comp (sheafExtendRestrictScalarsAdj (RingHom.id R) Z)),
    ← conjugateEquiv_comp _ ((inverseImageAdjunction f R).comp Adjunction.id),
    ← conjugateEquiv_comp _ (Adjunction.id.comp (inverseImageAdjunction f R))]
  simp only [conjugate_inverseImageExtendScalarsIso, conjugateEquiv_whiskerLeft,
    conjugateEquiv_whiskerRight, conjugate_sheafExtendScalarsIdIso_hom,
    conjugateEquiv_leftUnitor_hom, conjugateEquiv_rightUnitor_hom]
  apply NatTrans.ext
  funext F
  dsimp [directImageRestrictScalarsIso]
  simp only [Category.id_comp]
  apply Sheaf.hom_ext
  rfl

variable (φ : R →+* S) (ψ : S →+* T)

/-- Interchanging inverse image with extension by a composite ring map
equals the two successive actual scalar interchanges. -/
theorem inverseImageExtendScalarsIso_ringComp :
    (inverseImageExtendScalarsIso (ψ.comp φ) f).hom ≫
        whiskerLeft (inverseImage f R) (sheafExtendScalarsCompIso φ ψ Z).hom =
      whiskerRight (sheafExtendScalarsCompIso φ ψ X).hom (inverseImage f T) ≫
        (associator (sheafExtendScalars φ X) (sheafExtendScalars ψ X)
          (inverseImage f T)).hom ≫
        whiskerLeft (sheafExtendScalars φ X) (inverseImageExtendScalarsIso ψ f).hom ≫
        (associator (sheafExtendScalars φ X) (inverseImage f S)
          (sheafExtendScalars ψ Z)).inv ≫
        whiskerRight (inverseImageExtendScalarsIso φ f).hom (sheafExtendScalars ψ Z) ≫
        (associator (inverseImage f R) (sheafExtendScalars φ Z)
          (sheafExtendScalars ψ Z)).hom := by
  apply (conjugateEquiv
    ((inverseImageAdjunction f R).comp
      ((sheafExtendRestrictScalarsAdj φ Z).comp (sheafExtendRestrictScalarsAdj ψ Z)))
    ((sheafExtendRestrictScalarsAdj (ψ.comp φ) X).comp
      (inverseImageAdjunction f T))).injective
  rw [← conjugateEquiv_comp _
      ((inverseImageAdjunction f R).comp (sheafExtendRestrictScalarsAdj (ψ.comp φ) Z)),
    ← conjugateEquiv_comp _
      (((sheafExtendRestrictScalarsAdj φ X).comp
        (sheafExtendRestrictScalarsAdj ψ X)).comp (inverseImageAdjunction f T)),
    ← conjugateEquiv_comp _
      ((sheafExtendRestrictScalarsAdj φ X).comp
        ((sheafExtendRestrictScalarsAdj ψ X).comp (inverseImageAdjunction f T))),
    ← conjugateEquiv_comp _
      ((sheafExtendRestrictScalarsAdj φ X).comp
        ((inverseImageAdjunction f S).comp (sheafExtendRestrictScalarsAdj ψ Z))),
    ← conjugateEquiv_comp _
      (((sheafExtendRestrictScalarsAdj φ X).comp (inverseImageAdjunction f S)).comp
        (sheafExtendRestrictScalarsAdj ψ Z)),
    ← conjugateEquiv_comp _
      (((inverseImageAdjunction f R).comp (sheafExtendRestrictScalarsAdj φ Z)).comp
        (sheafExtendRestrictScalarsAdj ψ Z))]
  simp only [conjugate_inverseImageExtendScalarsIso, conjugate_sheafExtendScalarsCompIso_hom,
    conjugateEquiv_whiskerLeft, conjugateEquiv_whiskerRight,
    conjugateEquiv_associator_hom, conjugate_coefficient_associator_inv]
  apply NatTrans.ext
  funext F
  dsimp [directImageRestrictScalarsIso]
  simp only [Category.comp_id]
  apply Sheaf.hom_ext
  rfl

/-- The actual comparison with two successive coefficient extensions. -/
def inverseImageCompositeScalarsIso :
    sheafExtendScalars (ψ.comp φ) X ⋙ inverseImage f T ≅
      inverseImage f R ⋙ (sheafExtendScalars φ Z ⋙ sheafExtendScalars ψ Z) :=
  inverseImageExtendScalarsIso (ψ.comp φ) f ≪≫
    isoWhiskerLeft (inverseImage f R) (sheafExtendScalarsCompIso φ ψ Z)

/-- The constructed comparison is independent of whether coefficient
composition or geometric interchange is performed first. -/
theorem inverseImageCompositeScalarsIso_eq :
    inverseImageCompositeScalarsIso f φ ψ =
      isoWhiskerRight (sheafExtendScalarsCompIso φ ψ X) (inverseImage f T) ≪≫
        associator (sheafExtendScalars φ X) (sheafExtendScalars ψ X) (inverseImage f T) ≪≫
        isoWhiskerLeft (sheafExtendScalars φ X) (inverseImageExtendScalarsIso ψ f) ≪≫
        (associator (sheafExtendScalars φ X) (inverseImage f S)
          (sheafExtendScalars ψ Z)).symm ≪≫
        isoWhiskerRight (inverseImageExtendScalarsIso φ f) (sheafExtendScalars ψ Z) ≪≫
        associator (inverseImage f R) (sheafExtendScalars φ Z) (sheafExtendScalars ψ Z) := by
  apply Iso.ext
  simpa only [inverseImageCompositeScalarsIso, Iso.trans_hom, Iso.symm_hom,
    isoWhiskerLeft_hom, isoWhiskerRight_hom] using inverseImageExtendScalarsIso_ringComp f φ ψ

end Langlands.Geometry.EtaleInverseImage
