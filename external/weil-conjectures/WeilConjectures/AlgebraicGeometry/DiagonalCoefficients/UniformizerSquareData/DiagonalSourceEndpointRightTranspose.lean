/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.UniformizerSquareData.DiagonalSourceEndpointMaps
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.UniformizerSquareData.DiagonalDerivedSourceSquareMaps

/-! # Transpose of the right supported endpoint

Source: diagonal tower coefficient changes (1), scalar units and finite constants.
(blueprint: lem-diagonal-source-endpoint-right-transpose).
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

attribute [local instance] UniformizerSquareData.inverse_additive
  comp_preservesFiniteLimits comp_preservesFiniteColimits

attribute [local semireducible] UniformizerSquareData.quotientTranspose
  UniformizerSquareData.cyclicTranspose
  UniformizerSquareData.extendQuotientTranspose UniformizerSquareData.extendCyclicTranspose

-- Only elaboration is deferred; the normal kernel checks the resulting proof term.
local elab "constructed_exact " t:term : tactic => do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let e ← Lean.Elab.Term.elabTerm t none
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  goal.assign (← Lean.instantiateMVars e)
  Lean.Elab.Tactic.replaceMainGoal []

namespace UniformizerSquareData

variable {l : ℕ} [Fact l.Prime] {Y : Scheme.{u}}
  {E : PadicAlgCl.FiniteIntermediateField l} {π : PadicAlgCl.integers l E} {n : ℕ}
  {A : Type (u + 1)} [CommRing A] {hA : ((l ^ (n + 1) : ℕ) : A) = 0}
  (q : UniformizerSquareData l Y E π n A hA)

/-- The actual right endpoint composite has the prescribed cyclic transpose.
Source: coefficient changes (1). (blueprint: lem-diagonal-source-endpoint-right-transpose).
Proof: unfold the constructed right endpoint map. Naturality of the cyclic
adjunction hom equivalence moves the single source map through the transpose,
which is exactly the constructed cyclic extension. -/
theorem source_endpoint_right_transpose
    (s : q.quotientRight ≅ q.restriction ⋙ q.cyclicRight) :
    q.cyclicAdjunction.homEquiv _ _ (q.sourceEndpointRight s) =
      q.extendCyclicTranspose s q.cyclicTranspose := by
  constructed_exact q.cyclicAdjunction.homEquiv_naturality_right q.cyclicSource.hom
    ((DerivedCategory.singleFunctor _ 0).map q.sourceMap)

end UniformizerSquareData
end AlgebraicGeometry.ProEtale.DiagonalCoefficients
