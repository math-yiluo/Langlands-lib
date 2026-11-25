/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Cyclic.DiagonalCyclicCartierFrame

/-! # Shared exact realization of source and target endpoints

Source: diagonal tower coefficient changes (1), scalar compatibility and Ext realization.
(blueprint: def-diagonal-finite-realization-endpoints).
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

/-- Realize a source isomorphism, using the exact single comparison once. -/
def finiteSourceIso
    {R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] {A : Type (u + 1)} [CommRing A]
    {W : Scheme.{u}} (e : FiniteRealization R A W)
    {X : Modules R W} {Y : Sheaf (Scheme.ProEt.topology W) (ModuleCat.{u + 1} A)}
    {S : DerivedCategory (Modules R W)}
    (a : S ≅ (DerivedCategory.singleFunctor _ 0).obj X) (s : e.F.obj X ≅ Y) :
    e.F.mapDerivedCategory.obj S ≅ (DerivedCategory.singleFunctor _ 0).obj Y :=
  e.F.mapDerivedCategory.mapIso a ≪≫
    (e.F.mapDerivedCategorySingleFunctor 0).app X ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso s

/-- Realize a degree-two target, sharing its single and shift comparisons. -/
def finiteTargetMap
    {R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] {A : Type (u + 1)} [CommRing A]
    {W : Scheme.{u}} (e : FiniteRealization R A W)
    {X : Modules R W} {Y : Sheaf (Scheme.ProEt.topology W) (ModuleCat.{u + 1} A)}
    {T : DerivedCategory (Modules R W)}
    (t : T ⟶ ((DerivedCategory.singleFunctor _ 0).obj X)⟦(2 : ℤ)⟧)
    (line : e.F.obj X ≅ Y) :
    e.F.mapDerivedCategory.obj T ⟶ ((DerivedCategory.singleFunctor _ 0).obj Y)⟦(2 : ℤ)⟧ :=
  e.F.mapDerivedCategory.map t ≫
    (e.F.mapDerivedCategory.commShiftIso (2 : ℤ)).hom.app _ ≫
      ((e.F.mapDerivedCategorySingleFunctor 0).hom.app _ ≫
        (DerivedCategory.singleFunctor _ 0).map line.hom)⟦(2 : ℤ)⟧'

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
