/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.UniformizerSquareData.DiagonalDerivedSourceMaps

/-! # The two extensions of derived source transposes

Source: diagonal tower coefficient changes (1), scalar units and finite constants.
(blueprint: def-diagonal-derived-source-square-maps).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

-- Use the module-sheaf abelian structure of GeoCartierClass.
attribute [local instance 100000] sheafIsAbelian
attribute [local instance 200000] AlgebraicGeometry.ProEtale.diagonalAbSheafAbelian
attribute [local instance 300000] CommRing.toRing
attribute [local instance 400000] AlgebraicGeometry.ProEtale.diagonalModuleSheafAbelian

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] derivedScalars quotientLine quotientLineMap cyclicLine cyclicLineMap
  Functor.leftDerivedFunctor Mod.derivedExtendMapDerivedCategoryAdjunction
  HasDerivedCategory.standard DerivedCategory.singleFunctors HomotopyCategory.singleFunctors
  DerivedCategory.singleFunctorIsoCompQ
  Functor.mapDerivedCategory Functor.mapDerivedCategorySingleFunctor
  CondensedRing.lowerStar Profinite.continuousMapRingSheaf
  HasDerivedCategory.ofHasKInjectiveResolutions HasDerivedCategory.ofIsGrothendieckAbelian

attribute [local semireducible] UniformizerSquareData.cyclicEndpoints
  UniformizerSquareData.quotientEndpoints

attribute [local instance] UniformizerSquareData.inverse_additive
  comp_preservesFiniteLimits comp_preservesFiniteColimits

namespace UniformizerSquareData

variable {l : ℕ} [Fact l.Prime] {Y : Scheme.{u}}
  {E : PadicAlgCl.FiniteIntermediateField l} {π : PadicAlgCl.integers l E} {n : ℕ}
  {A : Type (u + 1)} [CommRing A] {hA : ((l ^ (n + 1) : ℕ) : A) = 0}
  (q : UniformizerSquareData l Y E π n A hA)

-- Retain the exact hom type of the supplied derived source square.
local elab "typeOf% " t:term:max : term => do
  let e ← Lean.Elab.Term.elabTerm t none
  return ← Lean.Meta.inferType e

/-- The common hom type of the two extended source transposes.
(blueprint: def-diagonal-derived-source-square-maps). -/
def sourceSquareHomType
    (s : q.quotientRight ≅ q.restriction ⋙ q.cyclicRight) : Type (u + 1) :=
  typeOf% (q.quotientTranspose ≫
    (Functor.mapDerivedCategoryNatIso s ≪≫
      (Functor.mapDerivedCategoryCompIso q.restriction q.cyclicRight).symm).hom.app _ ≫
    q.cyclicRight.mapDerivedCategory.map
      ((q.restriction.mapDerivedCategorySingleFunctor 0).hom.app _))

/-- Extend a quotient transpose across the given right comparison and single comparison.
(blueprint: def-diagonal-derived-source-square-maps). -/
@[irreducible] def extendQuotientTranspose
    (s : q.quotientRight ≅ q.restriction ⋙ q.cyclicRight)
    (f : q.quotientTransposeType) : q.sourceSquareHomType s :=
  f ≫ (Functor.mapDerivedCategoryNatIso s ≪≫
    (Functor.mapDerivedCategoryCompIso q.restriction q.cyclicRight).symm).hom.app _ ≫
    q.cyclicRight.mapDerivedCategory.map
      ((q.restriction.mapDerivedCategorySingleFunctor 0).hom.app _)

/-- Extend a cyclic transpose across the supplied source map.
(blueprint: def-diagonal-derived-source-square-maps). -/
@[irreducible] def extendCyclicTranspose
    (s : q.quotientRight ≅ q.restriction ⋙ q.cyclicRight)
    (f : q.cyclicTransposeType) : q.sourceSquareHomType s :=
  f ≫ q.cyclicRight.mapDerivedCategory.map
    ((DerivedCategory.singleFunctor _ 0).map q.sourceMap)

end UniformizerSquareData
end AlgebraicGeometry.ProEtale.DiagonalCoefficients
