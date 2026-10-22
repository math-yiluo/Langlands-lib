import Langlands.Geometry.EtalePullbackAdjunction
import Langlands.Geometry.EtaleRestrictionRightAdjoint
import Langlands.Cohomology.DerivedComparison

/-!
# Pullback on ordinary étale cohomology

Exactness and injective preservation allow étale restriction to carry injective
resolutions to injective resolutions. Deriving the section map gives the maps
on the previously constructed ordinary étale cohomology functors.
-/

noncomputable section

namespace Langlands.Geometry.EtalePullback

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.Cohomology

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X Y : Scheme.{u}} (f : Y ⟶ X) [Etale f]
variable (R : Type u) [CommRing R]

/-- Restriction of module sheaves is exact. -/
instance restriction_preservesHomology :
    (restriction f (ModuleCat.{u} R)).PreservesHomology := by
  infer_instance

/-- Restricting an injective resolution gives an injective resolution. -/
abbrev restrictedResolution {F : EtaleDerivedSections.ModuleSheaf X R}
    (I : InjectiveResolution F) :
    InjectiveResolution ((restriction f (ModuleCat.{u} R)).obj F) :=
  DerivedComparison.mapInjectiveResolution (restriction f (ModuleCat.{u} R)) I

/-- The comparison computed using a specified injective resolution. -/
def restrictionDerivedIsoOfResolution {F : EtaleDerivedSections.ModuleSheaf X R}
    (I : InjectiveResolution F) (q : ℕ) :
    ((restriction f (ModuleCat.{u} R) ⋙ EtaleDerivedSections.sections Y R).rightDerived q).obj F ≅
      (EtaleDerivedSections.cohomology Y R q).obj ((restriction f (ModuleCat.{u} R)).obj F) :=
  I.isoRightDerivedObj _ q ≪≫
    ((restrictedResolution f R I).isoRightDerivedObj (EtaleDerivedSections.sections Y R) q).symm

/-- The comparison is natural along every lift between resolutions. -/
theorem restrictionDerivedIsoOfResolution_naturality
    {F G : EtaleDerivedSections.ModuleSheaf X R} (α : F ⟶ G)
    (I : InjectiveResolution F) (J : InjectiveResolution G)
    (φ : I.cocomplex ⟶ J.cocomplex)
    (comm : I.ι.f 0 ≫ φ.f 0 = α ≫ J.ι.f 0) (q : ℕ) :
    ((restriction f (ModuleCat.{u} R) ⋙ EtaleDerivedSections.sections Y R).rightDerived q).map α ≫
        (restrictionDerivedIsoOfResolution f R J q).hom =
      (restrictionDerivedIsoOfResolution f R I q).hom ≫
        (EtaleDerivedSections.cohomology Y R q).map ((restriction f (ModuleCat.{u} R)).map α) := by
  have h₁ := InjectiveResolution.isoRightDerivedObj_hom_naturality α I J φ comm
    (restriction f (ModuleCat.{u} R) ⋙ EtaleDerivedSections.sections Y R) q
  have h₂ := InjectiveResolution.isoRightDerivedObj_inv_naturality
    ((restriction f (ModuleCat.{u} R)).map α)
    (restrictedResolution f R I) (restrictedResolution f R J)
    (((restriction f (ModuleCat.{u} R)).mapHomologicalComplex _).map φ)
    (DerivedComparison.mapInjectiveResolution_comm _ α I J φ comm)
    (EtaleDerivedSections.sections Y R) q
  dsimp only [restrictionDerivedIsoOfResolution, Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc, h₁]
  simp only [Category.assoc]
  erw [h₂]
  rfl

/-- Deriving the composite of restriction and sections computes cohomology
on the restricted sheaf. -/
def restrictionDerivedIso (q : ℕ) :
    (restriction f (ModuleCat.{u} R) ⋙ EtaleDerivedSections.sections Y R).rightDerived q ≅
      restriction f (ModuleCat.{u} R) ⋙ EtaleDerivedSections.cohomology Y R q :=
  NatIso.ofComponents
    (fun F => restrictionDerivedIsoOfResolution f R (injectiveResolution F) q)
    (fun {F G} α => restrictionDerivedIsoOfResolution_naturality f R α _ _
      (InjectiveResolution.desc α (injectiveResolution G) (injectiveResolution F))
      (InjectiveResolution.desc_commutes_zero α _ _) q)

/-- Apply the section map in each degree of the resolution. -/
def resolutionSectionsMap {F : EtaleDerivedSections.ModuleSheaf X R}
    (I : InjectiveResolution F) :
    ((EtaleDerivedSections.sections X R).mapHomologicalComplex _).obj I.cocomplex ⟶
      ((EtaleDerivedSections.sections Y R).mapHomologicalComplex _).obj
        (restrictedResolution f R I).cocomplex :=
  (NatTrans.mapHomologicalComplex (sectionsMap f R) _).app I.cocomplex

/-- Pullback on ordinary étale cohomology, natural in the coefficient sheaf. -/
def cohomologyMap (q : ℕ) :
    EtaleDerivedSections.cohomology X R q ⟶
      restriction f (ModuleCat.{u} R) ⋙ EtaleDerivedSections.cohomology Y R q :=
  NatTrans.rightDerived (sectionsMap f R) q ≫ (restrictionDerivedIso f R q).hom

/-- On the selected resolution, pullback is induced by the degreewise
section map and the identifications with resolution homology. -/
theorem cohomologyMap_app (F : EtaleDerivedSections.ModuleSheaf X R) (q : ℕ) :
    (cohomologyMap f R q).app F =
      ((injectiveResolution F).isoRightDerivedObj (EtaleDerivedSections.sections X R) q).hom ≫
        (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) q).map
          (resolutionSectionsMap f R (injectiveResolution F)) ≫
        ((restrictedResolution f R (injectiveResolution F)).isoRightDerivedObj
          (EtaleDerivedSections.sections Y R) q).inv := by
  dsimp only [cohomologyMap, NatTrans.comp_app]
  rw [InjectiveResolution.rightDerived_app_eq (sectionsMap f R) (injectiveResolution F)]
  dsimp only [restrictionDerivedIso, NatIso.ofComponents_hom_app,
    restrictionDerivedIsoOfResolution, Iso.trans_hom, Iso.symm_hom]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rfl

/-- The section chain map respects the maps from sections to degree-zero cycles. -/
theorem resolutionSectionsMap_toRightDerivedZero'
    {F : EtaleDerivedSections.ModuleSheaf X R} (I : InjectiveResolution F) :
    I.toRightDerivedZero' (EtaleDerivedSections.sections X R) ≫
        HomologicalComplex.cyclesMap (resolutionSectionsMap f R I) 0 =
      (sectionsMap f R).app F ≫
        (restrictedResolution f R I).toRightDerivedZero' (EtaleDerivedSections.sections Y R) := by
  apply (cancel_mono (HomologicalComplex.iCycles _ 0)).1
  simp only [Category.assoc, HomologicalComplex.cyclesMap_i,
    InjectiveResolution.toRightDerivedZero'_comp_iCycles_assoc]
  erw [(restrictedResolution f R I).toRightDerivedZero'_comp_iCycles]
  dsimp only [resolutionSectionsMap, NatTrans.mapHomologicalComplex_app_f]
  rw [DerivedComparison.mapInjectiveResolution_ι_f_zero]
  exact (sectionsMap f R).naturality (I.ι.f 0)

/-- Pullback agrees with the section map through the canonical degree-zero maps. -/
theorem cohomologyMap_toRightDerivedZero (F : EtaleDerivedSections.ModuleSheaf X R) :
    (EtaleDerivedSections.sections X R).toRightDerivedZero.app F ≫
        (cohomologyMap f R 0).app F =
      (sectionsMap f R).app F ≫
        (EtaleDerivedSections.sections Y R).toRightDerivedZero.app
          ((restriction f (ModuleCat.{u} R)).obj F) := by
  rw [(injectiveResolution F).toRightDerivedZero_eq (EtaleDerivedSections.sections X R),
    cohomologyMap_app,
    (restrictedResolution f R (injectiveResolution F)).toRightDerivedZero_eq
      (EtaleDerivedSections.sections Y R)]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  erw [HomologicalComplex.homologyπ_naturality_assoc]
  rw [← Category.assoc, resolutionSectionsMap_toRightDerivedZero']
  simp only [Category.assoc]
  rfl

/-- Under the canonical identifications of zeroth cohomology with sections,
pullback is the original section restriction. -/
theorem cohomologyMap_zero (F : EtaleDerivedSections.ModuleSheaf X R) :
    (cohomologyMap f R 0).app F ≫
        (EtaleDerivedSections.cohomologyZeroIso Y R).hom.app
          ((restriction f (ModuleCat.{u} R)).obj F) =
      (EtaleDerivedSections.cohomologyZeroIso X R).hom.app F ≫ (sectionsMap f R).app F := by
  apply (cancel_epi ((EtaleDerivedSections.sections X R).toRightDerivedZero.app F)).1
  rw [← Category.assoc, cohomologyMap_toRightDerivedZero]
  simp [EtaleDerivedSections.cohomologyZeroIso, Category.assoc,
    ← Category.assoc ((EtaleDerivedSections.sections X R).toRightDerivedZero.app F)]

/-- Pullback followed by a morphism of coefficients on the target scheme. -/
def cohomologyMapWithCoefficients (q : ℕ)
    {F : EtaleDerivedSections.ModuleSheaf X R} {G : EtaleDerivedSections.ModuleSheaf Y R}
    (α : (restriction f (ModuleCat.{u} R)).obj F ⟶ G) :
    (EtaleDerivedSections.cohomology X R q).obj F ⟶
      (EtaleDerivedSections.cohomology Y R q).obj G :=
  (cohomologyMap f R q).app F ≫ (EtaleDerivedSections.cohomology Y R q).map α

end Langlands.Geometry.EtalePullback
