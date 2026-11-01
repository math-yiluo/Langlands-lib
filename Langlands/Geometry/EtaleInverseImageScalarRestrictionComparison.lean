import Langlands.Geometry.EtaleInverseImageScalarCoherence
import Langlands.Geometry.EtaleInverseImageRestriction
import Langlands.Geometry.EtaleScalarExtensionPullback

/-! # Agreement with the existing etale-restriction scalar comparison -/

noncomputable section

universe u

namespace Langlands.Geometry.EtaleInverseImage

open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
open EtaleDirectImage EtaleCohomologyAction EtalePullback

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

private theorem conjugate_sameRightUniqueness
    {C D : Type*} [Category* C] [Category* D]
    {L L' : C ⥤ D} {G : D ⥤ C} (a : L ⊣ G) (b : L' ⊣ G) :
    conjugateEquiv b a (a.leftAdjointUniq b).hom = 𝟙 G := by
  ext Y
  apply ((a.homEquiv _ _).symm).injective
  simp only [Adjunction.homEquiv_counit]
  rw [conjugateEquiv_counit]
  simp [Adjunction.leftAdjointUniq_hom_app_counit]

variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
variable {X Z : Scheme.{u}} (f : Z ⟶ X) [Etale f]

/-- The geometric etale-restriction unit has the same underlying map after
restricting coefficient scalars. -/
theorem restrictionGeometricUnit_restrictScalars
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} S)) :
    (restrictionGeometricAdjunction f (ModuleCat.{u} R)).unit.app
        ((sheafRestrictScalars φ X).obj F) =
      (sheafRestrictScalars φ X).map
        ((restrictionGeometricAdjunction f (ModuleCat.{u} S)).unit.app F) := by
  apply Sheaf.hom_ext
  rfl

private def scalarRestrictionSourceAdjunction :
    sheafExtendScalars φ X ⋙ restriction f (ModuleCat.{u} S) ⊣
      sheafRestrictScalars φ Z ⋙ EtaleDirectImage.directImage f (ModuleCat.{u} R) :=
  (sheafExtendRestrictScalarsAdj φ X).comp
    (restrictionGeometricAdjunction f (ModuleCat.{u} S))

private def scalarRestrictionTargetAdjunction :
    restriction f (ModuleCat.{u} R) ⋙ sheafExtendScalars φ Z ⊣
      sheafRestrictScalars φ Z ⋙ EtaleDirectImage.directImage f (ModuleCat.{u} R) :=
  (restrictionGeometricAdjunction f (ModuleCat.{u} R)).comp
    (sheafExtendRestrictScalarsAdj φ Z)

private theorem scalarRestrictionComparison_unit
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :
    (scalarRestrictionSourceAdjunction φ f).unit.app F ≫
        (sheafRestrictScalars φ Z ⋙ EtaleDirectImage.directImage f (ModuleCat.{u} R)).map
          ((sheafExtendScalarsPullbackIso φ f).hom.app F) =
      (scalarRestrictionTargetAdjunction φ f).unit.app F := by
  dsimp only [scalarRestrictionSourceAdjunction, scalarRestrictionTargetAdjunction]
  rw [Adjunction.comp_unit_app, Adjunction.comp_unit_app]
  have hη := (restrictionGeometricAdjunction f (ModuleCat.{u} R)).unit.naturality
    ((sheafExtensionUnit φ X).app F)
  dsimp only [Functor.id_map, Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hη
  rw [← restrictionGeometricUnit_restrictScalars]
  change (sheafExtensionUnit φ X).app F ≫
      (restrictionGeometricAdjunction f (ModuleCat.{u} R)).unit.app
        ((sheafRestrictScalars φ X).obj ((sheafExtendScalars φ X).obj F)) ≫
      (EtaleDirectImage.directImage f (ModuleCat.{u} R)).map
        ((sheafRestrictScalars φ Z).map ((sheafExtendScalarsPullbackIso φ f).hom.app F)) =
    (restrictionGeometricAdjunction f (ModuleCat.{u} R)).unit.app F ≫
      (EtaleDirectImage.directImage f (ModuleCat.{u} R)).map
        ((sheafExtensionUnit φ Z).app ((restriction f (ModuleCat.{u} R)).obj F))
  rw [← Category.assoc]
  erw [hη]
  rw [Category.assoc, ← Functor.map_comp, sheafExtensionUnit_pullback]

/-- The old sheafification comparison is the unique comparison of the two
actual composite scalar/restriction adjunctions. -/
private theorem sheafExtendScalarsPullbackIso_eq_unique :
    sheafExtendScalarsPullbackIso φ f =
      Adjunction.leftAdjointUniq (scalarRestrictionSourceAdjunction φ f)
        (scalarRestrictionTargetAdjunction φ f) := by
  apply Iso.ext
  apply NatTrans.ext
  funext F
  apply ((scalarRestrictionSourceAdjunction φ f).homEquiv F _).injective
  rw [Adjunction.homEquiv_unit, scalarRestrictionComparison_unit]
  exact (Adjunction.homEquiv_leftAdjointUniq_hom_app _ _ F).symm

private theorem conjugate_restrictionScalarComparison :
    conjugateEquiv (scalarRestrictionTargetAdjunction φ f)
        (scalarRestrictionSourceAdjunction φ f)
        (sheafExtendScalarsPullbackIso φ f).hom = 𝟙 _ := by
  rw [sheafExtendScalarsPullbackIso_eq_unique]
  exact conjugate_sameRightUniqueness _ _

/-- After the actual inverse-image/restriction identifications, the general
scalar comparison equals the existing etale-restriction comparison. -/
theorem inverseImageExtendScalarsIso_restriction :
    (inverseImageExtendScalarsIso φ f).hom ≫
        whiskerRight (inverseImageIsoRestriction f R).hom (sheafExtendScalars φ Z) =
      whiskerLeft (sheafExtendScalars φ X) (inverseImageIsoRestriction f S).hom ≫
        (sheafExtendScalarsPullbackIso φ f).hom := by
  apply (conjugateEquiv (scalarRestrictionTargetAdjunction φ f)
    ((sheafExtendRestrictScalarsAdj φ X).comp (inverseImageAdjunction f S))).injective
  rw [← conjugateEquiv_comp _
      ((inverseImageAdjunction f R).comp (sheafExtendRestrictScalarsAdj φ Z)),
    ← conjugateEquiv_comp _ (scalarRestrictionSourceAdjunction φ f)]
  change conjugateEquiv
      ((restrictionGeometricAdjunction f (ModuleCat.{u} R)).comp
        (sheafExtendRestrictScalarsAdj φ Z))
      ((inverseImageAdjunction f R).comp (sheafExtendRestrictScalarsAdj φ Z))
      (whiskerRight (inverseImageIsoRestriction f R).hom (sheafExtendScalars φ Z)) ≫ _ =
    conjugateEquiv (scalarRestrictionTargetAdjunction φ f)
      (scalarRestrictionSourceAdjunction φ f) (sheafExtendScalarsPullbackIso φ f).hom ≫
      conjugateEquiv
        ((sheafExtendRestrictScalarsAdj φ X).comp
          (restrictionGeometricAdjunction f (ModuleCat.{u} S)))
        ((sheafExtendRestrictScalarsAdj φ X).comp (inverseImageAdjunction f S))
        (whiskerLeft (sheafExtendScalars φ X) (inverseImageIsoRestriction f S).hom)
  rw [conjugate_restrictionScalarComparison, conjugateEquiv_whiskerRight,
    conjugateEquiv_whiskerLeft, conjugate_inverseImageExtendScalarsIso]
  simp only [inverseImageIsoRestriction, conjugate_sameRightUniqueness,
    directImageRestrictScalarsIso, Iso.refl_inv, Category.id_comp]
  apply NatTrans.ext
  funext F
  simp

/-- Transport the general inverse-image scalar comparison to etale
restriction using the previously constructed adjoint-uniqueness isomorphisms. -/
def inverseImageExtendScalarsEtaleIso :
    sheafExtendScalars φ X ⋙ restriction f (ModuleCat.{u} S) ≅
      restriction f (ModuleCat.{u} R) ⋙ sheafExtendScalars φ Z :=
  isoWhiskerLeft (sheafExtendScalars φ X) (inverseImageIsoRestriction f S).symm ≪≫
    inverseImageExtendScalarsIso φ f ≪≫
    isoWhiskerRight (inverseImageIsoRestriction f R) (sheafExtendScalars φ Z)

theorem inverseImageExtendScalarsEtaleIso_eq :
    inverseImageExtendScalarsEtaleIso φ f = sheafExtendScalarsPullbackIso φ f := by
  apply Iso.ext
  change whiskerLeft (sheafExtendScalars φ X) (inverseImageIsoRestriction f S).inv ≫
      (inverseImageExtendScalarsIso φ f).hom ≫
      whiskerRight (inverseImageIsoRestriction f R).hom (sheafExtendScalars φ Z) = _
  rw [inverseImageExtendScalarsIso_restriction, ← whiskerLeft_comp_assoc]
  simp

end Langlands.Geometry.EtaleInverseImage
