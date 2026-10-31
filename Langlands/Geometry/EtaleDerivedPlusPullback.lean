import Langlands.Cohomology.DerivedPlusSource
import Langlands.Geometry.EtaleDerivedPullback
import Langlands.Geometry.EtaleDerivedSectionsPlus

/-! # Geometric pullback of bounded below derived etale sections -/

noncomputable section

namespace Langlands.Geometry.EtalePullback

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.Cohomology

universe u wX wY wT

variable {X Y : Scheme.{u}} (f : Y ⟶ X) [Etale f]
variable (R : Type u) [CommRing R]
variable [HasDerivedCategory.{wX} (EtaleDerivedSections.ModuleSheaf X R)]
  [HasDerivedCategory.{wY} (EtaleDerivedSections.ModuleSheaf Y R)]
  [HasDerivedCategory.{wT} (ModuleCat.{u} R)]

/-- Geometric pullback on the actual derived global sections of a coefficient
sheaf, natural in the sheaf. -/
def derivedSectionsMap :
    EtaleDerivedSectionsPlus.derivedSections X R ⟶
      restriction f (ModuleCat.{u} R) ⋙ EtaleDerivedSectionsPlus.derivedSections Y R :=
  DerivedPlusSource.derivedMap (EtaleDerivedSections.sections X R)
    (restriction f (ModuleCat.{u} R)) (EtaleDerivedSections.sections Y R) (sectionsMap f R)

/-- The actual section map on a resolution, extended to integer degrees. -/
def derivedResolutionSectionsMap {F : EtaleDerivedSections.ModuleSheaf X R}
    (I : InjectiveResolution F) :
    DerivedPlusSource.imageResolution (EtaleDerivedSections.sections X R) I ⟶
      DerivedPlusSource.imageResolution (EtaleDerivedSections.sections Y R)
        (restrictedResolution f R I) :=
  DerivedPlusSource.imageResolutionSquare (EtaleDerivedSections.sections X R)
    (restriction f (ModuleCat.{u} R)) (EtaleDerivedSections.sections Y R) (sectionsMap f R) I

/-- Any resolution computes geometric pullback after localization. -/
theorem derivedSectionsMap_app {F : EtaleDerivedSections.ModuleSheaf X R}
    (I : InjectiveResolution F) :
    (derivedSectionsMap f R).app F =
      (DerivedPlusSource.imageResolutionIso (EtaleDerivedSections.sections X R) I).hom ≫
        DerivedCategory.Plus.Q.map (derivedResolutionSectionsMap f R I) ≫
          (DerivedPlusSource.imageResolutionIso (EtaleDerivedSections.sections Y R)
            (restrictedResolution f R I)).inv :=
  DerivedPlusSource.derivedMap_app (EtaleDerivedSections.sections X R)
    (restriction f (ModuleCat.{u} R)) (EtaleDerivedSections.sections Y R) (sectionsMap f R) I

set_option backward.isDefEq.respectTransparency false in
/-- Every nonnegative cohomology map is the previously constructed ordinary
etale-cohomology pullback. -/
@[reassoc]
theorem derivedSectionsMap_homology
    (F : EtaleDerivedSections.ModuleSheaf X R) (q : ℕ) :
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) q).map
        ((derivedSectionsMap f R).app F) ≫
        (EtaleDerivedSectionsPlus.homologyNatIso Y R q).hom.app
          ((restriction f (ModuleCat.{u} R)).obj F) =
      (EtaleDerivedSectionsPlus.homologyNatIso X R q).hom.app F ≫
        (cohomologyMap f R q).app F := by
  rw [EtaleDerivedSectionsPlus.homologyNatIso_hom_app Y R (restrictedResolution f R
      (injectiveResolution F)) q,
    EtaleDerivedSectionsPlus.homologyNatIso_hom_app X R (injectiveResolution F) q,
    cohomologyMap_app]
  exact DerivedPlusSource.derivedMap_homology (EtaleDerivedSections.sections X R)
    (restriction f (ModuleCat.{u} R)) (EtaleDerivedSections.sections Y R) (sectionsMap f R)
    (injectiveResolution F) q

set_option backward.isDefEq.respectTransparency false in
/-- Degree-zero cohomology of geometric derived pullback is ordinary section
restriction under the canonical section identifications. -/
@[reassoc]
theorem derivedSectionsMap_zero (F : EtaleDerivedSections.ModuleSheaf X R) :
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0).map
        ((derivedSectionsMap f R).app F) ≫
        (EtaleDerivedSectionsPlus.homologyZeroIso Y R).hom.app
          ((restriction f (ModuleCat.{u} R)).obj F) =
      (EtaleDerivedSectionsPlus.homologyZeroIso X R).hom.app F ≫ (sectionsMap f R).app F := by
  simp only [EtaleDerivedSectionsPlus.homologyZeroIso, Iso.trans_hom, NatTrans.comp_app,
    Category.assoc]
  erw [derivedSectionsMap_homology_assoc f R F 0]
  rw [cohomologyMap_zero]

/-- Geometric derived pullback followed by a map of target coefficients. -/
def derivedSectionsMapWithCoefficients
    {F : EtaleDerivedSections.ModuleSheaf X R} {G : EtaleDerivedSections.ModuleSheaf Y R}
    (α : (restriction f (ModuleCat.{u} R)).obj F ⟶ G) :
    (EtaleDerivedSectionsPlus.derivedSections X R).obj F ⟶
      (EtaleDerivedSectionsPlus.derivedSections Y R).obj G :=
  (derivedSectionsMap f R).app F ≫ (EtaleDerivedSectionsPlus.derivedSections Y R).map α

set_option backward.isDefEq.respectTransparency false in
/-- Adding a target coefficient map recovers the ordinary cohomology map with
the same coefficient map. -/
theorem derivedSectionsMapWithCoefficients_homology
    {F : EtaleDerivedSections.ModuleSheaf X R} {G : EtaleDerivedSections.ModuleSheaf Y R}
    (α : (restriction f (ModuleCat.{u} R)).obj F ⟶ G) (q : ℕ) :
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) q).map
        (derivedSectionsMapWithCoefficients f R α) ≫
        (EtaleDerivedSectionsPlus.homologyNatIso Y R q).hom.app G =
      (EtaleDerivedSectionsPlus.homologyNatIso X R q).hom.app F ≫
        cohomologyMapWithCoefficients f R q α := by
  have h := (EtaleDerivedSectionsPlus.homologyNatIso Y R q).hom.naturality α
  simp only [Functor.comp_map] at h
  simp only [derivedSectionsMapWithCoefficients, Functor.map_comp, Category.assoc]
  rw [h, derivedSectionsMap_homology_assoc]
  rfl

end Langlands.Geometry.EtalePullback
