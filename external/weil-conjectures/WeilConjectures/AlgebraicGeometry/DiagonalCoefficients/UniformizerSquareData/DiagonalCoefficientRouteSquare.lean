/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.UniformizerSquareData.DiagonalCoefficientRouteEquations
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalExtMateSquare

/-! # The proved endpoint criterion for the concrete coefficient routes

Source: diagonal tower coefficient changes (1), derived naturality.
(blueprint: lem-diagonal-coefficient-route-square).
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
  Functor.leftDerivedFunctor Mod.derivedExtendMapDerivedCategoryAdjunction
  DerivedCategory.singleFunctorIsoCompQ
  DerivedCategory HasDerivedCategory.ofHasKInjectiveResolutions
  CondensedRing.lowerStar Profinite.continuousMapRingSheaf
  HasDerivedCategory.standard HasDerivedCategory.ofIsGrothendieckAbelian
  DerivedCategory.singleFunctors HomotopyCategory.singleFunctors

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] Ext.homEquiv Ext.comp Ext.mk₀ Ext.mapExactFunctor
attribute [local semireducible] CyclicCartierFrame.reduce

set_option linter.defProp false in
/-- The fully proved endpoint criterion specialized to the supplied coefficient
routes. Its four arguments are the independent source comparison, target
comparison, and two realization identities. These independent hypotheses remain
proof arguments to the criterion.
Source: coefficient changes (1) (blueprint: lem-diagonal-coefficient-route-square).
Proof: specialize the proved generic naturality and Ext/Hom calculation to the
actual restriction functor, derived mate, source and root-line endpoints. -/
@[irreducible] def UniformizerSquareData.endpointSquare
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    (E : PadicAlgCl.FiniteIntermediateField l) (π : PadicAlgCl.integers l E) (n : ℕ)
    (A : Type (u + 1)) [CommRing A]
    (hA : ((l ^ (n + 1) : ℕ) : A) = 0)
    (q : UniformizerSquareData l Y E π n A hA) :=
  finiteCoefficient_extSquare_of_endpoints q.restriction
    q.cyclicFunctor q.quotientFunctor
    (fun s : q.quotientRight ≅ q.restriction ⋙ q.cyclicRight ↦ q.comparison s)
    (fun s ↦ q.RestrictionNormalized s)
    q.cyclicSource q.quotientSource q.cyclicTarget q.quotientTarget
    q.route.initial.delta
    (q.cyclic.reduce l Y n q.route.initial.delta)
    (finiteRealizedClass (L := quotientLine l E π n) (l ^ (n + 1)) hA Y
      q.eW q.lineW.endpoint.iso q.sourceComparison.iso q.route.final.delta)
    q.sourceMap q.lineMap

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
