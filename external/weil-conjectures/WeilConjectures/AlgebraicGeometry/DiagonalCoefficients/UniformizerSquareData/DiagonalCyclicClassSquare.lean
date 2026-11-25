/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.UniformizerSquareData.DiagonalCoefficientTargetSquare
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.UniformizerSquareData.DiagonalCoefficientRouteRealization

/-! # Applying the cyclic realization identity

Source: diagonal tower coefficient changes (1), independent endpoint and realization steps.
(blueprint: lem-diagonal-cyclic-class-square).
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
/-- Apply the cyclic realization identity to the proved criterion from the preceding step.
The other independent proof arguments remain available in its inferred type.
Source: coefficient changes (1) (blueprint: lem-diagonal-cyclic-class-square).
Proof: supply the named endpoint or realization theorem to the preceding proved
criterion. This is a proof term; it constructs no mathematical data. -/
@[irreducible] def UniformizerSquareData.cyclicSquare
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    (E : PadicAlgCl.FiniteIntermediateField l) (π : PadicAlgCl.integers l E) (n : ℕ)
    (A : Type (u + 1)) [CommRing A]
    (hA : ((l ^ (n + 1) : ℕ) : A) = 0)
    (q : UniformizerSquareData l Y E π n A hA) :=
  UniformizerSquareData.targetSquare l Y E π n A hA q
    (UniformizerSquareData.cyclic_realization l Y E π n A hA q)

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
