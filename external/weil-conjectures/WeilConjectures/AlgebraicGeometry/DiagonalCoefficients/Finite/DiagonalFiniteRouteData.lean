/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Finite.DiagonalFiniteRouteDataCore
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Finite.DiagonalFiniteRealizationComposition

/-! # Bundled finite realization endpoints and their proved arrow calculation

Source: diagonal tower coefficient changes (1), scalar compatibility and Ext realization.
(blueprint: def-diagonal-finite-route-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u v u' v'
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

-- Use the module-sheaf abelian structure of GeoCartierClass.
attribute [local instance 100000] sheafIsAbelian
attribute [local instance 200000] AlgebraicGeometry.ProEtale.diagonalAbSheafAbelian
attribute [local instance 300000] CommRing.toRing
attribute [local instance 400000] AlgebraicGeometry.ProEtale.diagonalModuleSheafAbelian

attribute [local irreducible] geoCartierConstant geoCartierLine
  quotientLine quotientLineMap cyclicLine cyclicLineMap
  derivedScalars QuotientLineRealization finiteRealizedClass CyclicCartierFrame.reduce
  Functor.mapDerivedCategory Functor.mapDerivedCategorySingleFunctor Endpoint.shift
  Mod.extendScalars AlgebraicGeometry.ProEtale.upperStarFromPoint
  Functor.leftDerivedFunctor Mod.derivedExtendMapDerivedCategoryAdjunction
  DerivedCategory.singleFunctorIsoCompQ
  HasDerivedCategory.standard DerivedCategory.singleFunctors HomotopyCategory.singleFunctors

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] Ext.homEquiv

section
variable
  {R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj R] [IsCommMonObj R] {A : Type (u + 1)} [CommRing A]
  (N : ℕ) (hA : (N : A) = 0) (Y : Scheme.{u})
  {L : ∀ X : Scheme.{u}, Modules R X}
  (eW : FiniteRealization R A (diagonalSurface Y))
  (line : eW.F.obj (L (diagonalSurface Y)) ≅ geoCartierLine A N hA (diagonalSurface Y))
  (s : eW.F.obj (source R Y) ≅
    (lowerStar (ModuleCat.{u + 1} A) (diagonalImmersion Y)).obj
      (geoCartierConstant A (ProjectiveLine Y)))
  {B : Type*} [Category B] (F : B ⥤ DerivedCategory (Modules R (diagonalSurface Y)))
  {S T : B}
  (a : F.obj S ≅ (DerivedCategory.singleFunctor _ 0).obj (source R Y))
  (t : F.obj T ⟶ ((DerivedCategory.singleFunctor _ 0).obj
    (L (diagonalSurface Y)))⟦(2 : ℤ)⟧)

/-- Construct the route data by exact realization, with its generic arrow proof. -/
def finiteRouteData :=
  FiniteRouteData.mk
    (classes := finiteRealizedArrowMap (N := N) (hA := hA) (Y := Y)
      (eW := eW) (line := line) (s := s))
    (compatible := routeArrowCompatible F a t)
    (F ⋙ eW.F.mapDerivedCategory) (finiteSourceIso eW a s) (finiteTargetMap eW t line)
    (fun β α h ↦ finiteRealization_composition (L := L) N hA Y eW line s F a t β α h)

end

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
