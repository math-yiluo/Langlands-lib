/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Integral.IntegralTowerPullbackSquareData
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.ConstantTowerDerivedSquare
/-! # Exact transport with normalized original boundary maps -/
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

attribute [local instance] NormalizedIntegralTowerSquare.additiveF
  NormalizedIntegralTowerSquare.limitsF NormalizedIntegralTowerSquare.colimitsF
  NormalizedIntegralTowerSquare.additiveP NormalizedIntegralTowerSquare.limitsP
  NormalizedIntegralTowerSquare.colimitsP

/-- An ordinary sheaf class square induces the corresponding normalized tower class square.
Proof: use congruence to replace the source realization and the units boundary on the left,
and the integer boundary and target realization on the right. Exact-derived constant-tower
transport gives the equality between these normalized composites. Apply transitivity.
Source: blueprint classes proof (2)
(blueprint: lem-sp-integral-tower-pullback-square). -/
theorem normalized_integral_tower_square {X Y : Scheme.{u}}
    [hDiagY : HasDerivedCategory.{u + 1} (DiagonalAb Y)]
    [hDiagX : HasDerivedCategory.{u + 1} (DiagonalAb X)]
    [hAbY : HasDerivedCategory.{u + 2} (Ab Y)]
    [hAbX : HasDerivedCategory.{u + 2} (Ab X)]
    (d : NormalizedIntegralTowerSquare X Y) :
    d.P.mapDerivedCategory.map d.classY.towerClass ≫ d.uDerived =
      d.iDerived ≫ d.classX.towerClass := by
  have hleft := congrArg₂
    (fun (c : (DerivedCategory.singleFunctor (Ab Y) 0).obj (integers Y) ⟶
        ((DerivedCategory.singleFunctor (Ab Y) 0).obj (units Y))⟦(1 : ℤ)⟧)
      (v : UnitsDerivedPullType d.P) ↦ d.P.mapDerivedCategory.map c ≫ v)
    d.classY.realization d.uDerived_eq
  have hright := congrArg₂
    (fun (i : IntegerDerivedPullType d.P)
      (c : (DerivedCategory.singleFunctor (Ab X) 0).obj (integers X) ⟶
        ((DerivedCategory.singleFunctor (Ab X) 0).obj (units X))⟦(1 : ℤ)⟧) ↦ i ≫ c)
    d.iDerived_eq.symm d.classX.realization.symm
  exact hleft.trans
    ((constant_tower_derived_square d.F d.P d.τ d.z d.a d.s d.t d.hs d.ht
      d.classY.sheafClass d.classX.sheafClass d.commutes).trans hright)

end AlgebraicGeometry.ProEtale.SpTowerClasses
