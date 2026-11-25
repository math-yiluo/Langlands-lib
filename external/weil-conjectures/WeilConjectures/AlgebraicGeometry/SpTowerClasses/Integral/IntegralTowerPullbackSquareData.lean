/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Integral.IntegralTowerRealizationData
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

/-- An exact inverse-image square with ordinary endpoints and normalized derived boundary maps.
Source: blueprint classes proof (2)
(blueprint: def-sp-integral-tower-pullback-square-data). -/
structure NormalizedIntegralTowerSquare (X Y : Scheme.{u})
    [hDiagY : HasDerivedCategory.{u + 1} (DiagonalAb Y)]
    [hDiagX : HasDerivedCategory.{u + 1} (DiagonalAb X)]
    [hAbY : HasDerivedCategory.{u + 2} (Ab Y)]
    [hAbX : HasDerivedCategory.{u + 2} (Ab X)]
    where
  F : DiagonalAb Y ⥤ DiagonalAb X
  P : Ab Y ⥤ Ab X
  [additiveF : F.Additive]
  [limitsF : PreservesFiniteLimits F]
  [colimitsF : PreservesFiniteColimits F]
  [additiveP : P.Additive]
  [limitsP : PreservesFiniteLimits P]
  [colimitsP : PreservesFiniteColimits P]
  τ : F ⋙ constant X ≅ constant Y ⋙ P
  z : F.obj ((constantSheaf (Scheme.ProEt.topology Y) AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))) ⟶
    ((constantSheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
  a : F.obj (Scheme.proEtaleUnitsSheaf Y) ⟶ Scheme.proEtaleUnitsSheaf X
  s : P.obj (integers Y) ⟶ integers X
  t : P.obj (units Y) ⟶ units X
  hs : s = τ.inv.app ((constantSheaf (Scheme.ProEt.topology Y) AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))) ≫ (constant X).map z
  ht : τ.hom.app (Scheme.proEtaleUnitsSheaf Y) ≫ t = (constant X).map a
  classY : @IntegralConstantClass Y hDiagY hAbY
  classX : @IntegralConstantClass X hDiagX hAbX
  commutes : mapSingleArrow F 1 classY.sheafClass ≫
      ((DerivedCategory.singleFunctor (DiagonalAb X) 0).map a)⟦(1 : ℤ)⟧' =
    (DerivedCategory.singleFunctor (DiagonalAb X) 0).map z ≫ classX.sheafClass
  iDerived : IntegerDerivedPullType (hAbY := hAbY) (hAbX := hAbX) P
  uDerived : UnitsDerivedPullType (hAbY := hAbY) (hAbX := hAbX) P
  iDerived_eq : iDerived = normalizedIntegerComparison
    (hAbY := hAbY) (hAbX := hAbX) P s
  uDerived_eq : uDerived = normalizedUnitsComparison
    (hAbY := hAbY) (hAbX := hAbX) P t

end AlgebraicGeometry.ProEtale.SpTowerClasses
