/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Integral.TowerIntegralPullbackData
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Line.LineBundleProEtaleClassPullback
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Integral.IntegralTowerPullbackSquareData
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

attribute [local instance 100000] abDerived

/-- The normalized square for a line bundle and its geometric pullback.
Construct the functors and endpoints explicitly. Picard cohomology naturality gives the
ordinary class square; all comparison equalities are the defining formulas.
Source: blueprint classes proof (2)
(blueprint: def-sp-line-bundle-tower-pullback-square). -/
def towerIntegral_normalizedSquare {X Y : Scheme.{u}} (f : X ⟶ Y)
    (L : Y.Modules) [Scheme.Modules.IsInvertible L] :
    NormalizedIntegralTowerSquare X Y where
  F := upperStar AddCommGrpCat.{u + 1} f
  P := abPull f
  additiveF := by infer_instance
  limitsF := by infer_instance
  colimitsF := by infer_instance
  additiveP := abPull_additive f
  limitsP := abPull_limits f
  colimitsP := abPull_colimits f
  τ := towerIntegral_constantPullIso f
  z := towerIntegral_integerSheafPull f
  a := towerIntegral_unitsSheafPull f
  s := integerPull f
  t := unitsPull f
  hs := towerIntegral_integerPull_iso f
  ht := towerIntegral_unitsPull_iso f
  classY := towerIntegral_realizedClass Y (Scheme.Pic.ofIsInvertible L)
  classX := towerIntegral_realizedClass X
    (Scheme.Pic.ofIsInvertible ((Scheme.Modules.pullback f).obj L))
  commutes := lineBundle_proEtaleClass_pullback f L (towerIntegral_unitsSheafPull f)
    (towerIntegral_unitsPull_adjoint f)
  iDerived := integerDerivedPull f
  uDerived := unitsDerivedPull f
  iDerived_eq := by rfl
  uDerived_eq := by rfl

end AlgebraicGeometry.ProEtale.SpTowerClasses
