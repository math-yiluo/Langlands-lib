/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.ConstantTowerDerivedSquare

/-! # Realization data for integral constant-tower classes -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale.SpTowerClasses
attribute [local irreducible] Functor.mapDerivedCategory mapSingleArrow
  DerivedCategory.singleFunctors

/-- Realize a degree-one ordinary sheaf arrow as an arrow between constant towers.
Source: blueprint classes proof (2)
(blueprint: def-sp-integral-tower-realization-data). -/
def normalizedConstantArrow (T : Scheme.{u})
    [hDiag : HasDerivedCategory.{u + 1} (DiagonalAb T)]
    [hAb : HasDerivedCategory.{u + 2} (Ab T)]
    (h : (DerivedCategory.singleFunctor (DiagonalAb T) 0).obj
      ((constantSheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ))) ⟶
      ((DerivedCategory.singleFunctor (DiagonalAb T) 0).obj
        (Scheme.proEtaleUnitsSheaf T))⟦(1 : ℤ)⟧) :
    (DerivedCategory.singleFunctor (Ab T) 0).obj (integers T) ⟶
      ((DerivedCategory.singleFunctor (Ab T) 0).obj (units T))⟦(1 : ℤ)⟧ :=
  @mapSingleArrow
    (DiagonalAb T) (by infer_instance) (diagonalAbSheafAbelian T)
    (Ab T) (by infer_instance) (towerAbelian T) hDiag hAb
    (constant T) (constantAdditive T) (constantLimits T) (constantColimits T)
    ((constantSheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
    (Scheme.proEtaleUnitsSheaf T) 1 h
/-- An ordinary integral class together with its specified constant-tower realization.
Source: blueprint classes proof (2)
(blueprint: def-sp-integral-tower-realization-data). -/
structure IntegralConstantClass (T : Scheme.{u})
    [hDiag : HasDerivedCategory.{u + 1} (DiagonalAb T)]
    [hAb : HasDerivedCategory.{u + 2} (Ab T)] where
  sheafClass : (DerivedCategory.singleFunctor (DiagonalAb T) 0).obj
      ((constantSheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ))) ⟶
      ((DerivedCategory.singleFunctor (DiagonalAb T) 0).obj
        (Scheme.proEtaleUnitsSheaf T))⟦(1 : ℤ)⟧
  towerClass : (DerivedCategory.singleFunctor (Ab T) 0).obj (integers T) ⟶
    ((DerivedCategory.singleFunctor (Ab T) 0).obj (units T))⟦(1 : ℤ)⟧
  realization : towerClass = @normalizedConstantArrow T hDiag hAb sheafClass

/-- The morphism type of the derived integer comparison, with fixed localization models.
Source: blueprint classes proof (2)
(blueprint: def-sp-integral-tower-realization-data). -/
def IntegerDerivedPullType {X Y : Scheme.{u}}
    [hAbY : HasDerivedCategory.{u + 2} (Ab Y)]
    [hAbX : HasDerivedCategory.{u + 2} (Ab X)]
    (P : Ab Y ⥤ Ab X) [P.Additive] [PreservesFiniteLimits P]
    [PreservesFiniteColimits P] :=
  P.mapDerivedCategory.obj ((DerivedCategory.singleFunctor (Ab Y) 0).obj (integers Y)) ⟶
    (DerivedCategory.singleFunctor (Ab X) 0).obj (integers X)

/-- The morphism type of the derived units comparison, including its shift by one.
Source: blueprint classes proof (2)
(blueprint: def-sp-integral-tower-realization-data). -/
def UnitsDerivedPullType {X Y : Scheme.{u}}
    [hAbY : HasDerivedCategory.{u + 2} (Ab Y)]
    [hAbX : HasDerivedCategory.{u + 2} (Ab X)]
    (P : Ab Y ⥤ Ab X) [P.Additive] [PreservesFiniteLimits P]
    [PreservesFiniteColimits P] :=
  P.mapDerivedCategory.obj
    (((DerivedCategory.singleFunctor (Ab Y) 0).obj (units Y))⟦(1 : ℤ)⟧) ⟶
    ((DerivedCategory.singleFunctor (Ab X) 0).obj (units X))⟦(1 : ℤ)⟧

/-- The canonical derived integer comparison associated to an ordinary tower map.
Source: blueprint classes proof (2)
(blueprint: def-sp-integral-tower-realization-data). -/
def normalizedIntegerComparison {X Y : Scheme.{u}}
    [hAbY : HasDerivedCategory.{u + 2} (Ab Y)]
    [hAbX : HasDerivedCategory.{u + 2} (Ab X)]
    (P : Ab Y ⥤ Ab X) [P.Additive] [PreservesFiniteLimits P]
    [PreservesFiniteColimits P] (s : P.obj (integers Y) ⟶ integers X) :
    IntegerDerivedPullType P :=
  derivedSingleEndpoint P s

/-- The canonical shifted derived units comparison associated to an ordinary tower map.
Source: blueprint classes proof (2)
(blueprint: def-sp-integral-tower-realization-data). -/
def normalizedUnitsComparison {X Y : Scheme.{u}}
    [hAbY : HasDerivedCategory.{u + 2} (Ab Y)]
    [hAbX : HasDerivedCategory.{u + 2} (Ab X)]
    (P : Ab Y ⥤ Ab X) [P.Additive] [PreservesFiniteLimits P]
    [PreservesFiniteColimits P] (t : P.obj (units Y) ⟶ units X) :
    UnitsDerivedPullType P :=
  derivedShiftedSingleEndpoint P t

attribute [local instance 100000] abDerived

/-- The line-bundle class with its defining ordinary sheaf realization.
The realization equality follows by unfolding the two definitions.
Source: blueprint classes proof (2)
(blueprint: def-sp-integral-tower-realization-data). -/
def towerIntegral_realizedClass (T : Scheme.{u}) (L : T.Pic) :
    IntegralConstantClass T where
  sheafClass := lineBundleEtaleClass T L
  towerClass := lineBundleClass T L
  realization := by rfl

end AlgebraicGeometry.ProEtale.SpTowerClasses
