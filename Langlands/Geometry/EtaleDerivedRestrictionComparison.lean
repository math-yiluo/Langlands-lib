import Langlands.Cohomology.DerivedPlusSourceTransform
import Langlands.Geometry.EtaleDerivedResolutionComparison
import Langlands.Geometry.EtaleDerivedPlusPullback

/-! # Agreement of geometric derived pullback with etale restriction -/

noncomputable section

universe u wX wZ wR

namespace Langlands.Geometry.EtaleDerivedGlobalPullback

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open EtaleInverseImage EtaleDerivedSections
open Langlands.Cohomology Langlands.Cohomology.DerivedPlus
open Langlands.Cohomology.DerivedPlusSource

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X Z : Scheme.{u}} (f : Z ⟶ X) [Etale f]
  (R : Type u) [CommRing R]
variable [HasDerivedCategory.{wX} (ModuleSheaf X R)]
  [HasDerivedCategory.{wZ} (ModuleSheaf Z R)]
  [HasDerivedCategory.{wR} (ModuleCat.{u} R)]

/-- The geometric derived pullback from the actual adjunction agrees with
the earlier etale-restriction construction through the actual coefficient
isomorphism, as an equality of natural transformations. -/
theorem sheafDerivedPullback_restriction_eq :
    sheafDerivedPullback f R ≫
      Functor.whiskerRight (inverseImageIsoRestriction f R).hom
        (EtaleDerivedSectionsPlus.derivedSections Z R) =
    EtalePullback.derivedSectionsMap f R := by
  change sheafDerivedPullback f R ≫
      Functor.whiskerRight (inverseImageIsoRestriction f R).hom
        (derivedComplex (sections Z R)) =
    derivedMap (sections X R) (EtalePullback.restriction f (ModuleCat.{u} R))
      (sections Z R) (EtalePullback.sectionsMap f R)
  rw [sheafDerivedPullback_eq_derivedMap, derivedMap_whiskerRight,
    sectionsPullback_restriction_eq]

/-- Componentwise agreement of the two actual derived pullback maps. -/
@[reassoc] theorem sheafDerivedPullback_restriction (F : ModuleSheaf X R) :
    (sheafDerivedPullback f R).app F ≫
      (EtaleDerivedSectionsPlus.derivedSections Z R).map
        ((inverseImageIsoRestriction f R).hom.app F) =
    (EtalePullback.derivedSectionsMap f R).app F :=
  congrArg (fun τ => τ.app F) (sheafDerivedPullback_restriction_eq f R)

/-- An actual arrow isomorphism identifies geometric derived pullback with
the earlier etale-restriction map using the constructed coefficient iso. -/
def sheafDerivedPullbackRestrictionIso (F : ModuleSheaf X R) :
    Arrow.mk ((sheafDerivedPullback f R).app F) ≅
      Arrow.mk ((EtalePullback.derivedSectionsMap f R).app F) :=
  Arrow.isoMk' _ _ (Iso.refl _)
    ((EtaleDerivedSectionsPlus.derivedSections Z R).mapIso
      ((inverseImageIsoRestriction f R).app F))
    (by
      simpa only [Iso.refl_hom, Category.id_comp, Functor.mapIso_hom, Iso.app_hom]
        using (sheafDerivedPullback_restriction f R F).symm)

/-- Every nonnegative geometric cohomology pullback agrees with the earlier
ordinary etale-cohomology pullback through the actual coefficient iso. -/
@[reassoc] theorem cohomologyPullback_restriction (q : ℕ) (F : ModuleSheaf X R) :
    (cohomologyPullback f R q).app F ≫
      (cohomology Z R q).map ((inverseImageIsoRestriction f R).hom.app F) =
    (EtalePullback.cohomologyMap f R q).app F := by
  have hn := (EtaleDerivedSectionsPlus.homologyNatIso Z R q).hom.naturality
    ((inverseImageIsoRestriction f R).hom.app F)
  dsimp only [Functor.comp_map] at hn
  simp only [cohomologyPullback, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.whiskerLeft_app, Category.id_comp,
    Category.assoc]
  rw [← hn, ← Functor.map_comp_assoc, sheafDerivedPullback_restriction,
    EtalePullback.derivedSectionsMap_homology]
  simp only [Iso.inv_hom_id_app_assoc]

/-- Equality of the actual natural transformations on ordinary cohomology. -/
theorem cohomologyPullback_restriction_eq (q : ℕ) :
    cohomologyPullback f R q ≫
      Functor.whiskerRight (inverseImageIsoRestriction f R).hom (cohomology Z R q) =
    EtalePullback.cohomologyMap f R q := by
  apply NatTrans.ext
  funext F
  exact cohomologyPullback_restriction f R q F

/-- The corresponding actual isomorphism of ordinary cohomology arrows. -/
def cohomologyPullbackRestrictionIso (q : ℕ) (F : ModuleSheaf X R) :
    Arrow.mk ((cohomologyPullback f R q).app F) ≅
      Arrow.mk ((EtalePullback.cohomologyMap f R q).app F) :=
  Arrow.isoMk' _ _ (Iso.refl _)
    ((cohomology Z R q).mapIso ((inverseImageIsoRestriction f R).app F))
    (by
      simpa only [Iso.refl_hom, Category.id_comp, Functor.mapIso_hom, Iso.app_hom]
        using (cohomologyPullback_restriction f R q F).symm)

end Langlands.Geometry.EtaleDerivedGlobalPullback
