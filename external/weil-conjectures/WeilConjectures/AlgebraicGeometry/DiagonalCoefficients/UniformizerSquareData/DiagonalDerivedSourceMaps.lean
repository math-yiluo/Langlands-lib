/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.UniformizerSquareData.DiagonalOrdinarySourceMaps

/-! # Constructed derived source transpose maps

Source: diagonal tower coefficient changes (1), scalar units and finite constants.
(blueprint: def-diagonal-derived-source-maps).
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

-- Preserve the actual category data of the existing endpoint construction.
local elab "typeOf% " t:term:max : term => do
  let e ← Lean.Elab.Term.elabTerm t none
  return ← Lean.Meta.inferType e

/-- The actual hom type of the cyclic source transpose.
(blueprint: def-diagonal-derived-source-maps). -/
def cyclicTransposeType : Type (u + 1) :=
  typeOf% (q.cyclicAdjunction.homEquiv _ _ q.cyclicSource.hom)

/-- The actual hom type of the successive source transpose.
(blueprint: def-diagonal-derived-source-maps). -/
def quotientTransposeType : Type (u + 1) :=
  typeOf% (q.quotientAdjunction.homEquiv _ _ q.quotientSource.hom)

/-- The actual cyclic source transpose as a named ordinary derived morphism.
(blueprint: def-diagonal-derived-source-maps). -/
@[irreducible] def cyclicTranspose : q.cyclicTransposeType :=
  q.cyclicAdjunction.homEquiv _ _ q.cyclicSource.hom

/-- The actual successive source transpose, retaining the bundled category data.
(blueprint: def-diagonal-derived-source-maps). -/
@[irreducible] def quotientTranspose : q.quotientTransposeType :=
  q.quotientAdjunction.homEquiv _ _ q.quotientSource.hom

/-- The normalized ordinary cyclic source map in degree zero.
(blueprint: def-diagonal-derived-source-maps). -/
@[irreducible] def cyclicSingleNormalized : q.cyclicTransposeType :=
  (DerivedCategory.singleFunctor _ 0).map q.cyclicOrdinary ≫
    (q.cyclicRight.mapDerivedCategorySingleFunctor 0).inv.app _

/-- The normalized ordinary successive source map in degree zero.
(blueprint: def-diagonal-derived-source-maps). -/
@[irreducible] def quotientSingleNormalized : q.quotientTransposeType :=
  (DerivedCategory.singleFunctor _ 0).map q.quotientOrdinary ≫
    (q.quotientRight.mapDerivedCategorySingleFunctor 0).inv.app _

end UniformizerSquareData
end AlgebraicGeometry.ProEtale.DiagonalCoefficients
