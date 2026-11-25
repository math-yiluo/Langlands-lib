/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.UniformizerSquareData.DiagonalDerivedSourceSquareMaps
import all WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalSourceAdjunctionTransport
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.UniformizerSquareData.DiagonalOrdinarySourceNormalization

/-! # The single image of the ordinary source square

Source: diagonal tower coefficient changes (1), exact scalar and finite-realization adjunctions.
(blueprint: lem-diagonal-single-source-square).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

-- Use the module-sheaf abelian structure of GeoCartierClass.
attribute [local instance 100000] sheafIsAbelian
attribute [local instance 200000] AlgebraicGeometry.ProEtale.diagonalAbSheafAbelian
attribute [local instance 300000] CommRing.toRing
attribute [local instance 400000] AlgebraicGeometry.ProEtale.diagonalModuleSheafAbelian

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] geoCartierConstant geoCartierLine QuotientLineRealization
  finiteRealizedClass Endpoint.shift Mod.extendScalars
  AlgebraicGeometry.ProEtale.upperStarFromPoint Ext.homEquiv
  DerivedCategory derivedScalars quotientLine quotientLineMap cyclicLine cyclicLineMap
  Functor.leftDerivedFunctor Mod.derivedExtendMapDerivedCategoryAdjunction
  HasDerivedCategory.standard DerivedCategory.singleFunctors HomotopyCategory.singleFunctors
  DerivedCategory.singleFunctorIsoCompQ
  Functor.mapDerivedCategory Functor.mapDerivedCategorySingleFunctor
  CondensedRing.lowerStar Profinite.continuousMapRingSheaf
  HasDerivedCategory.ofHasKInjectiveResolutions HasDerivedCategory.ofIsGrothendieckAbelian

attribute [local instance] UniformizerSquareData.inverse_additive
  comp_preservesFiniteLimits comp_preservesFiniteColimits

attribute [local semireducible] UniformizerSquareData.cyclicEndpoints
  UniformizerSquareData.quotientEndpoints UniformizerSquareData.finiteAdjunction
  ScalarCompatibility.compositeAdjunction UniformizerSquareData.quotientAdjunction

namespace UniformizerSquareData

variable {l : ℕ} [Fact l.Prime] {Y : Scheme.{u}}
  {E : PadicAlgCl.FiniteIntermediateField l} {π : PadicAlgCl.integers l E} {n : ℕ}
  {A : Type (u + 1)} [CommRing A] {hA : ((l ^ (n + 1) : ℕ) : A) = 0}
  (q : UniformizerSquareData l Y E π n A hA)

attribute [local semireducible] quotientSingleNormalized cyclicSingleNormalized
  extendQuotientTranspose extendCyclicTranspose

/-- Exact single comparisons carry the ordinary source square to derived morphisms.
Source: coefficient changes (1). (blueprint: lem-diagonal-single-source-square).
Proof: apply naturality of the exact single comparisons to the normalized ordinary
source equation, first for the right comparison and then for the source map. -/
theorem source_single_square
    (s : q.quotientRight ≅ q.restriction ⋙ q.cyclicRight)
    (hs : q.RestrictionNormalized s) :
    q.extendQuotientTranspose s q.quotientSingleNormalized =
      q.extendCyclicTranspose s q.cyclicSingleNormalized := by
  exact single_comparison_square q.quotientRight q.restriction q.cyclicRight s _ _ _
    q.quotientOrdinary q.cyclicOrdinary q.sourceMap (q.ordinary_source_eq s hs)

end UniformizerSquareData
end AlgebraicGeometry.ProEtale.DiagonalCoefficients
