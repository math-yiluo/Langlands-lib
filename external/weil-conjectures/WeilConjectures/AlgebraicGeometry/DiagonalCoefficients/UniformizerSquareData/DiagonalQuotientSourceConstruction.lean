/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.UniformizerSquareData.DiagonalQuotientTransposeMap

/-! # Constructor comparison for the successive supported endpoint

Source: diagonal tower coefficient changes (1), exact scalar and finite-realization adjunctions.
(blueprint: lem-diagonal-quotient-source-construction).
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

attribute [local semireducible] UniformizerSquareData.cyclicEndpoints
  UniformizerSquareData.quotientEndpoints

attribute [local instance] UniformizerSquareData.inverse_additive
  comp_preservesFiniteLimits comp_preservesFiniteColimits

attribute [local semireducible] UniformizerSquareData.finiteAdjunction
  ScalarCompatibility.compositeAdjunction

-- Elaborate the fully specified term independently; the kernel still checks its
-- conversion to the stated equality when checking the theorem declaration.
local elab "constructed_exact " t:term : tactic => do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let e ← Lean.Elab.Term.elabTerm t none
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let e ← Lean.instantiateMVars e
  goal.assign e
  Lean.Elab.Tactic.replaceMainGoal []

namespace UniformizerSquareData

variable {l : ℕ} [Fact l.Prime] {Y : Scheme.{u}}
  {E : PadicAlgCl.FiniteIntermediateField l} {π : PadicAlgCl.integers l E} {n : ℕ}
  {A : Type (u + 1)} [CommRing A] {hA : ((l ^ (n + 1) : ℕ) : A) = 0}
  (q : UniformizerSquareData l Y E π n A hA)

attribute [local semireducible] quotientAdjunction quotientTranspose quotientExplicitTranspose

/-- The bundled quotient transpose is its explicit finite source construction.
Source: coefficient changes (1). (blueprint: lem-diagonal-quotient-source-construction).
Proof: project the supported field of finiteRouteData in quotientEndpoints. This
field is finiteSourceIso of the supplied composite scalar endpoint and finite
source comparison. The named collected adjunction unfolds to the same explicit
adjunction. Reflexivity on the named transpose proves the constructor equality. -/
theorem quotient_source_constructor : q.quotientTranspose = q.quotientExplicitTranspose := by
  constructed_exact Eq.refl q.quotientTranspose

end UniformizerSquareData
end AlgebraicGeometry.ProEtale.DiagonalCoefficients
