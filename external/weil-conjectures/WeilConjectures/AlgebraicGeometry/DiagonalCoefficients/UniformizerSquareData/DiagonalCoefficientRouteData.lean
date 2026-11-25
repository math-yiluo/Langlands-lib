/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Uniformizer.DiagonalUniformizerRootFrame
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Finite.DiagonalFiniteRouteData
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.ScalarCompatibility.DiagonalScalarArrowComposition

/-! # Explicit endpoint bundles for cyclic and successive coefficient routes

Source: diagonal tower coefficient changes (1), scalar compatibility and Ext realization.
(blueprint: def-diagonal-coefficient-route-data).
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

/-- The cyclic route's actual endpoints and universal realization calculation. -/
@[irreducible] def UniformizerSquareData.cyclicEndpoints
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    (E : PadicAlgCl.FiniteIntermediateField l) (π : PadicAlgCl.integers l E) (n : ℕ)
    (A : Type (u + 1)) [CommRing A]
    (hA : ((l ^ (n + 1) : ℕ) : A) = 0)
    (q : UniformizerSquareData l Y E π n A hA) :=
  finiteRouteData (L := cyclicLine l n) (l ^ (n + 1))
    (cartierResidue_cast l (n + 1)) Y q.cyclic.eW q.cyclic.lineEndpoint.iso
    q.cyclic.sourceComparison.iso
    (derivedScalars (cyclicMap l n) (diagonalSurface Y))
    q.cyclic.supported.iso (q.cyclic.line.shift (cyclicMap l n))

/-- The successive route's actual endpoints and universal realization calculation. -/
@[irreducible] def UniformizerSquareData.quotientEndpoints
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    (E : PadicAlgCl.FiniteIntermediateField l) (π : PadicAlgCl.integers l E) (n : ℕ)
    (A : Type (u + 1)) [CommRing A]
    (hA : ((l ^ (n + 1) : ℕ) : A) = 0)
    (q : UniformizerSquareData l Y E π n A hA) :=
  finiteRouteData (L := quotientLine l E π n) (l ^ (n + 1)) hA Y
    q.eW q.lineW.endpoint.iso q.sourceComparison.iso
    (ScalarCompatibility.compositeFunctor q.route.first q.route.second)
    (ScalarCompatibility.compositeSource q.route.first q.route.second)
    (ScalarCompatibility.compositeTarget q.route.first q.route.second)

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
