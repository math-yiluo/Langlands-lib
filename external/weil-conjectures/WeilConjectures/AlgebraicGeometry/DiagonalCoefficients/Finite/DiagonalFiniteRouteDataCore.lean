/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Finite.DiagonalFiniteRealizationEndpoints

/-! # Shared input predicates and finite realization record

Source: diagonal tower coefficient changes (1), scalar compatibility and Ext realization.
(blueprint: def-diagonal-finite-route-data-core).
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

/-- The input square for a supported endpoint and a target map. -/
def routeArrowCompatible
    {B : Type*} {C : Type*} [Category B] [Category C]
    {S T : B} {X Y : C} (F : B ⥤ C) (a : F.obj S ≅ X) (t : F.obj T ⟶ Y)
    (β : S ⟶ T) (α : X ⟶ Y) : Prop :=
  F.map β ≫ t = a.hom ≫ α

/-- Endpoint data with a proved realization method for an arbitrary family of
compatible arrows. Its functor and endpoints are fixed before an arrow is given. -/
structure FiniteRouteData
    {B : Type*} {C : Type*} [Category B] [Category C] {S T : B} {X Y : C} {I : Type*}
    (classes : I → (X ⟶ Y)) (compatible : (S ⟶ T) → I → Prop) where
  functor : B ⥤ C
  supported : functor.obj S ≅ X
  lineMap : functor.obj T ⟶ Y
  realize : ∀ (β : S ⟶ T) (α : I), compatible β α →
    supported.hom ≫ classes α = functor.map β ≫ lineMap

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

/-- The explicit family of derived representatives, shared by name in the bundle. -/
def finiteRealizedArrowMap
    (α : (DerivedCategory.singleFunctor (Modules R (diagonalSurface Y)) 0).obj
      (source R Y) ⟶ ((DerivedCategory.singleFunctor _ 0).obj
        (L (diagonalSurface Y)))⟦(2 : ℤ)⟧) :=
  (finiteRealizedClass (L := L) N hA Y eW line s α).hom

end

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
