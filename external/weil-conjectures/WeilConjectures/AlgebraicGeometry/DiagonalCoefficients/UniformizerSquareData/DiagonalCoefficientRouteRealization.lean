/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.UniformizerSquareData.DiagonalCoefficientRouteEndpoints

/-! # Realization identities for finite coefficient routes

Source: diagonal tower coefficient changes (1), scalar compatibility and Ext realization.
(blueprint: lem-diagonal-coefficient-route-realization).
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
  derivedScalars QuotientLineRealization finiteRealizedClass
  Functor.mapDerivedCategory Functor.mapDerivedCategorySingleFunctor Endpoint.shift
  Mod.extendScalars AlgebraicGeometry.ProEtale.upperStarFromPoint
  Functor.leftDerivedFunctor Mod.derivedExtendMapDerivedCategoryAdjunction
  DerivedCategory.singleFunctorIsoCompQ
  DerivedCategory HasDerivedCategory.ofHasKInjectiveResolutions
  CondensedRing.lowerStar Profinite.continuousMapRingSheaf
  HasDerivedCategory.standard HasDerivedCategory.ofIsGrothendieckAbelian
  DerivedCategory.singleFunctors HomotopyCategory.singleFunctors

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] Ext.homEquiv

-- Primitive projection keeps the bundle's stored category arguments.
local elab "routeField% " i:num d:term:max : term => do
  let e ← Lean.Elab.Term.elabTerm d none
  return Lean.mkProj ``FiniteRouteData i.getNat e

set_option linter.defProp false in
/-- The cyclic realized class is the image of the supplied initial arrow. -/
@[irreducible] def UniformizerSquareData.cyclic_realization
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    (E : PadicAlgCl.FiniteIntermediateField l) (π : PadicAlgCl.integers l E) (n : ℕ)
    (A : Type (u + 1)) [CommRing A]
    (hA : ((l ^ (n + 1) : ℕ) : A) = 0)
    (q : UniformizerSquareData l Y E π n A hA) :=
  (routeField% 3 (q.cyclicEndpoints l Y E π n A hA)) q.route.initial.delta
    (q.cyclic.supported.iso.inv ≫
      (derivedScalars (cyclicMap l n) (diagonalSurface Y)).map q.route.initial.delta ≫
        q.cyclic.line.shift (cyclicMap l n))
    (q.cyclic.supported.iso.hom_inv_id_assoc
      ((derivedScalars (cyclicMap l n) (diagonalSurface Y)).map q.route.initial.delta ≫
        q.cyclic.line.shift (cyclicMap l n))).symm

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
