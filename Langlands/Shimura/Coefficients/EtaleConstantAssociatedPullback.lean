import Langlands.Shimura.Coefficients.EtaleAssociatedPullback
import Langlands.Geometry.EtaleConstantPullback

/-! # Etale restriction of constant-module associated coefficient sheaves -/

noncomputable section

universe u

namespace Langlands.Shimura.Coefficients

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.Geometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X Z : Scheme.{u}} (f : Z ⟶ X) [Etale f]
variable (R : Type u) [CommRing R]
variable {G : Type u} [Group G]

/-- The constant-sheaf comparison preserves every coefficient group operator. -/
def etaleConstantActionPullback :
    (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).mapAction G ⋙
        (EtalePullback.restriction f (ModuleCat.{u} R)).mapAction G ≅
      (constantSheaf Z.smallEtaleTopology (ModuleCat.{u} R)).mapAction G :=
  (Functor.mapActionComp G _ _).symm ≪≫
    Functor.mapActionCongr G (EtalePullback.constantPullbackIso f (ModuleCat.{u} R))

@[simp] theorem etaleConstantActionPullback_hom_hom (M : Action (ModuleCat.{u} R) G) :
    ((etaleConstantActionPullback f R).hom.app M).hom =
      (EtalePullback.constantPullbackIso f (ModuleCat.{u} R)).hom.app M.V := by
  simp [etaleConstantActionPullback]

@[simp] theorem etaleConstantActionPullback_inv_hom (M : Action (ModuleCat.{u} R) G) :
    ((etaleConstantActionPullback f R).inv.app M).hom =
      (EtalePullback.constantPullbackIso f (ModuleCat.{u} R)).inv.app M.V := by
  simp [etaleConstantActionPullback]

variable (Y : Action X.Etale G)

/-- Constant-module associated sheaves commute with actual etale restriction. -/
def etaleConstantAssociatedPullback :
    etaleAssociatedFunctor (R := R) X Y ⋙ EtalePullback.restriction f (ModuleCat.{u} R) ≅
      etaleAssociatedFunctor Z ((etaleTorsorPullbackFunctor f G).obj Y) :=
  Functor.isoWhiskerLeft ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).mapAction G)
      (etaleAssociatedPullback f R Y) ≪≫
    Functor.isoWhiskerRight (etaleConstantActionPullback f R)
      (associatedFunctor Z.smallEtaleTopology ((etaleTorsorPullbackFunctor f G).obj Y))

/-- The constant-coefficient comparison has the canonical invariant inclusion. -/
@[reassoc] theorem etaleConstantAssociatedPullback_hom_inclusion
    (M : Action (ModuleCat.{u} R) G) :
    (etaleConstantAssociatedPullback f R Y).hom.app M ≫
        inclusion Z.smallEtaleTopology ((etaleTorsorPullbackFunctor f G).obj Y)
          (((constantSheaf Z.smallEtaleTopology (ModuleCat.{u} R)).mapAction G).obj M) =
      (EtalePullback.restriction f (ModuleCat.{u} R)).map
          (inclusion X.smallEtaleTopology Y
            (((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).mapAction G).obj M)) ≫
        (etaleProductSheafPullback f R Y.V).hom.app
            ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj M.V) ≫
          (productSheaf Z.smallEtaleTopology ((etaleObjectPullback f).obj Y.V)).map
            ((EtalePullback.constantPullbackIso f (ModuleCat.{u} R)).hom.app M.V) := by
  change ((etaleAssociatedPullback f R Y).hom.app
      (((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).mapAction G).obj M) ≫
      (associatedFunctor Z.smallEtaleTopology ((etaleTorsorPullbackFunctor f G).obj Y)).map
        ((etaleConstantActionPullback f R).hom.app M)) ≫ _ = _
  rw [Category.assoc]
  erw [inclusion_natural Z.smallEtaleTopology ((etaleTorsorPullbackFunctor f G).obj Y)
    ((etaleConstantActionPullback f R).hom.app M)]
  rw [← Category.assoc]
  erw [etaleAssociatedPullback_hom_inclusion f R Y
    (((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).mapAction G).obj M)]
  rw [etaleConstantActionPullback_hom_hom, Category.assoc]
  rfl

/-- The inverse comparison recovers the restricted original invariant inclusion. -/
@[reassoc] theorem etaleConstantAssociatedPullback_inv_inclusion
    (M : Action (ModuleCat.{u} R) G) :
    (etaleConstantAssociatedPullback f R Y).inv.app M ≫
        (EtalePullback.restriction f (ModuleCat.{u} R)).map
          (inclusion X.smallEtaleTopology Y
            (((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).mapAction G).obj M)) =
      inclusion Z.smallEtaleTopology ((etaleTorsorPullbackFunctor f G).obj Y)
          (((constantSheaf Z.smallEtaleTopology (ModuleCat.{u} R)).mapAction G).obj M) ≫
        (productSheaf Z.smallEtaleTopology ((etaleObjectPullback f).obj Y.V)).map
            ((EtalePullback.constantPullbackIso f (ModuleCat.{u} R)).inv.app M.V) ≫
          (etaleProductSheafPullback f R Y.V).inv.app
            ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj M.V) := by
  change ((associatedFunctor Z.smallEtaleTopology ((etaleTorsorPullbackFunctor f G).obj Y)).map
        ((etaleConstantActionPullback f R).inv.app M) ≫
      (etaleAssociatedPullback f R Y).inv.app
        (((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).mapAction G).obj M)) ≫ _ = _
  rw [Category.assoc]
  erw [etaleAssociatedPullback_inv_inclusion f R Y
    (((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).mapAction G).obj M)]
  rw [← Category.assoc]
  erw [inclusion_natural Z.smallEtaleTopology ((etaleTorsorPullbackFunctor f G).obj Y)
    ((etaleConstantActionPullback f R).inv.app M)]
  rw [etaleConstantActionPullback_inv_hom, Category.assoc]
  rfl

end Langlands.Shimura.Coefficients
