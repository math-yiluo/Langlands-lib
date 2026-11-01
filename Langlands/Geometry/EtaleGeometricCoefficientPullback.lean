import Langlands.Geometry.EtaleDerivedRestrictionComparison
import Langlands.Geometry.EtaleDerivedSheafCoherence
import Langlands.Geometry.EtaleDerivedGlobalZero

/-! # Geometric cohomological pullback with target coefficients -/

noncomputable section

universe u wX wZ wV wR

namespace Langlands.Geometry.EtaleDerivedGlobalPullback

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open EtaleInverseImage EtaleDerivedSections

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X Z V : Scheme.{u}} (f : Z ⟶ X) (R : Type u) [CommRing R]

/-- Actual global-section pullback followed by an arbitrary target
coefficient map, for any scheme morphism. -/
def sectionsPullbackWithCoefficients {F : ModuleSheaf X R} {G : ModuleSheaf Z R}
    (α : (inverseImage f R).obj F ⟶ G) :
    (sections X R).obj F ⟶ (sections Z R).obj G :=
  (sectionsPullback f R).app F ≫ (sections Z R).map α

variable [HasDerivedCategory.{wX} (ModuleSheaf X R)]
  [HasDerivedCategory.{wZ} (ModuleSheaf Z R)]
  [HasDerivedCategory.{wR} (ModuleCat.{u} R)]

/-- Actual geometric derived pullback followed by the target coefficient
morphism. No etaleness hypothesis is needed. -/
def sheafDerivedPullbackWithCoefficients
    {F : ModuleSheaf X R} {G : ModuleSheaf Z R}
    (α : (inverseImage f R).obj F ⟶ G) :
    (EtaleDerivedSectionsPlus.derivedSections X R).obj F ⟶
      (EtaleDerivedSectionsPlus.derivedSections Z R).obj G :=
  (sheafDerivedPullback f R).app F ≫
    (EtaleDerivedSectionsPlus.derivedSections Z R).map α

/-- The corresponding actual ordinary cohomology map in every nonnegative
 degree, using the same geometric coefficient map. -/
def cohomologyPullbackWithCoefficients (q : ℕ)
    {F : ModuleSheaf X R} {G : ModuleSheaf Z R}
    (α : (inverseImage f R).obj F ⟶ G) :
    (cohomology X R q).obj F ⟶ (cohomology Z R q).obj G :=
  (cohomologyPullback f R q).app F ≫ (cohomology Z R q).map α

/-- The geometric derived transformation recovers the constructed ordinary
cohomology transformation under the canonical homology identifications. -/
@[reassoc] theorem sheafDerivedPullback_homology (q : ℕ) (F : ModuleSheaf X R) :
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) q).map
        ((sheafDerivedPullback f R).app F) ≫
      (EtaleDerivedSectionsPlus.homologyNatIso Z R q).hom.app
        ((inverseImage f R).obj F) =
    (EtaleDerivedSectionsPlus.homologyNatIso X R q).hom.app F ≫
      (cohomologyPullback f R q).app F := by
  simp only [cohomologyPullback, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Category.id_comp,
    Iso.hom_inv_id_app_assoc]

/-- Homology of the actual derived coefficient map is ordinary geometric
cohomology with precisely the same coefficient map. -/
@[reassoc] theorem sheafDerivedPullbackWithCoefficients_homology (q : ℕ)
    {F : ModuleSheaf X R} {G : ModuleSheaf Z R}
    (α : (inverseImage f R).obj F ⟶ G) :
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) q).map
        (sheafDerivedPullbackWithCoefficients f R α) ≫
      (EtaleDerivedSectionsPlus.homologyNatIso Z R q).hom.app G =
    (EtaleDerivedSectionsPlus.homologyNatIso X R q).hom.app F ≫
      cohomologyPullbackWithCoefficients f R q α := by
  have hn := (EtaleDerivedSectionsPlus.homologyNatIso Z R q).hom.naturality α
  dsimp only [Functor.comp_map] at hn
  simp only [sheafDerivedPullbackWithCoefficients, Functor.map_comp, Category.assoc]
  rw [hn, sheafDerivedPullback_homology_assoc]
  rfl

/-- Degree-zero homology recovers actual global-section pullback with the
specified target coefficients. -/
@[reassoc] theorem sheafDerivedPullbackWithCoefficients_zero
    {F : ModuleSheaf X R} {G : ModuleSheaf Z R}
    (α : (inverseImage f R).obj F ⟶ G) :
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0).map
        (sheafDerivedPullbackWithCoefficients f R α) ≫
      (EtaleDerivedSectionsPlus.homologyZeroIso Z R).hom.app G =
    (EtaleDerivedSectionsPlus.homologyZeroIso X R).hom.app F ≫
      sectionsPullbackWithCoefficients f R α := by
  have hn := (EtaleDerivedSectionsPlus.homologyZeroIso Z R).hom.naturality α
  dsimp only [Functor.comp_map] at hn
  simp only [sheafDerivedPullbackWithCoefficients, Functor.map_comp, Category.assoc]
  rw [hn, sheafDerivedPullback_zero_assoc]
  rfl

/-- Naturality in source coefficients, with inverse image on the actual
source coefficient morphism. -/
theorem sheafDerivedPullbackWithCoefficients_precomp
    {F F' : ModuleSheaf X R} {G : ModuleSheaf Z R}
    (α : (inverseImage f R).obj F ⟶ G) (a : F' ⟶ F) :
    sheafDerivedPullbackWithCoefficients f R ((inverseImage f R).map a ≫ α) =
      (EtaleDerivedSectionsPlus.derivedSections X R).map a ≫
        sheafDerivedPullbackWithCoefficients f R α := by
  dsimp only [sheafDerivedPullbackWithCoefficients]
  rw [Functor.map_comp, ← Category.assoc]
  simpa only [Category.assoc, Functor.comp_map] using congrArg
    (fun b => b ≫ (EtaleDerivedSectionsPlus.derivedSections Z R).map α)
    ((sheafDerivedPullback f R).naturality a).symm

/-- Naturality in target coefficients. -/
theorem sheafDerivedPullbackWithCoefficients_postcomp
    {F : ModuleSheaf X R} {G G' : ModuleSheaf Z R}
    (α : (inverseImage f R).obj F ⟶ G) (a : G ⟶ G') :
    sheafDerivedPullbackWithCoefficients f R (α ≫ a) =
      sheafDerivedPullbackWithCoefficients f R α ≫
        (EtaleDerivedSectionsPlus.derivedSections Z R).map a := by
  simp only [sheafDerivedPullbackWithCoefficients, Functor.map_comp, Category.assoc]

/-- The geometric identity coefficient map induces the identity in D-plus. -/
@[simp] theorem sheafDerivedPullbackWithCoefficients_id (F : ModuleSheaf X R) :
    sheafDerivedPullbackWithCoefficients (𝟙 X) R
      ((inverseImageId R X).hom.app F) = 𝟙 _ :=
  sheafDerivedPullback_id R F

variable [HasDerivedCategory.{wV} (ModuleSheaf V R)]

/-- Arbitrary successive geometric maps with target coefficients compose
using the constructed inverse-image composition isomorphism. -/
theorem sheafDerivedPullbackWithCoefficients_comp (g : V ⟶ Z)
    {F : ModuleSheaf X R} {G : ModuleSheaf Z R} {H : ModuleSheaf V R}
    (α : (inverseImage f R).obj F ⟶ G)
    (β : (inverseImage g R).obj G ⟶ H) :
    sheafDerivedPullbackWithCoefficients f R α ≫
      sheafDerivedPullbackWithCoefficients g R β =
    sheafDerivedPullbackWithCoefficients (g ≫ f) R
      ((inverseImageComp R f g).inv.app F ≫ (inverseImage g R).map α ≫ β) := by
  dsimp only [sheafDerivedPullbackWithCoefficients]
  rw [← sheafDerivedPullback_comp R f g F]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id_app]
  erw [(EtaleDerivedSectionsPlus.derivedSections V R).map_id]
  rw [Category.id_comp]
  simpa only [Category.assoc, Functor.comp_map] using congrArg
    (fun a => (sheafDerivedPullback f R).app F ≫ a ≫
      (EtaleDerivedSectionsPlus.derivedSections V R).map β)
    ((sheafDerivedPullback g R).naturality α)

omit [HasDerivedCategory.{wV} (ModuleSheaf V R)] in
/-- Along an etale map, geometric pullback with transported target
coefficients is exactly the earlier restriction-based derived map. -/
theorem sheafDerivedPullbackWithCoefficients_restriction [Etale f]
    {F : ModuleSheaf X R} {G : ModuleSheaf Z R}
    (α : (EtalePullback.restriction f (ModuleCat.{u} R)).obj F ⟶ G) :
    sheafDerivedPullbackWithCoefficients f R
      ((inverseImageIsoRestriction f R).hom.app F ≫ α) =
    EtalePullback.derivedSectionsMapWithCoefficients f R α := by
  simp only [sheafDerivedPullbackWithCoefficients,
    EtalePullback.derivedSectionsMapWithCoefficients, Functor.map_comp,
    ← Category.assoc, sheafDerivedPullback_restriction]

omit [HasDerivedCategory.{wV} (ModuleSheaf V R)] in
/-- The same exact agreement holds for every ordinary cohomology degree. -/
theorem cohomologyPullbackWithCoefficients_restriction [Etale f] (q : ℕ)
    {F : ModuleSheaf X R} {G : ModuleSheaf Z R}
    (α : (EtalePullback.restriction f (ModuleCat.{u} R)).obj F ⟶ G) :
    cohomologyPullbackWithCoefficients f R q
      ((inverseImageIsoRestriction f R).hom.app F ≫ α) =
    EtalePullback.cohomologyMapWithCoefficients f R q α := by
  simp only [cohomologyPullbackWithCoefficients,
    EtalePullback.cohomologyMapWithCoefficients, Functor.map_comp,
    ← Category.assoc, cohomologyPullback_restriction]

end Langlands.Geometry.EtaleDerivedGlobalPullback
