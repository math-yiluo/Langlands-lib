/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.UniformizerSquareData.DiagonalCoefficientRouteSquare

/-! # Actual supported endpoint morphisms

Source: diagonal tower coefficient changes (1), scalar units and finite constants.
(blueprint: def-diagonal-source-endpoint-maps).
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

-- Extract the existing criterion's actual endpoint hom type or morphism.
local elab "endpointComponent% " f:term:max s:term:max k:num : term => do
  let ef ← Lean.Elab.Term.elabTerm f none
  let es ← Lean.Elab.Term.elabTerm s none
  let .forallE _ domain _ _ ← Lean.Meta.whnf (← Lean.Meta.inferType ef)
    | throwError "criterion has no source hypothesis"
  let conjunction ← Lean.Meta.whnf (Lean.mkApp domain.getAppArgs.back! es)
  unless conjunction.isAppOf ``And do
    throwError "criterion source is not a conjunction"
  let equation := conjunction.getAppArgs.back!
  unless equation.isAppOf ``Eq do
    throwError "criterion source is not an equality"
  return equation.getAppArgs[k.getNat]!

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

namespace UniformizerSquareData

variable {l : ℕ} [Fact l.Prime] {Y : Scheme.{u}}
  {E : PadicAlgCl.FiniteIntermediateField l} {π : PadicAlgCl.integers l E} {n : ℕ}
  {A : Type (u + 1)} [CommRing A] {hA : ((l ^ (n + 1) : ℕ) : A) = 0}
  (q : UniformizerSquareData l Y E π n A hA)

/-- The actual common hom type in the supported endpoint criterion.
(blueprint: def-diagonal-source-endpoint-maps). -/
def sourceEndpointHomType
    (s : q.quotientRight ≅ q.restriction ⋙ q.cyclicRight) : Type (u + 1) :=
  endpointComponent% (endpointSquare l Y E π n A hA q) s 0

/-- The actual left morphism in the supported endpoint criterion.
(blueprint: def-diagonal-source-endpoint-maps). -/
@[irreducible] def sourceEndpointLeft
    (s : q.quotientRight ≅ q.restriction ⋙ q.cyclicRight) : q.sourceEndpointHomType s :=
  endpointComponent% (endpointSquare l Y E π n A hA q) s 1

/-- The actual right morphism in the supported endpoint criterion.
(blueprint: def-diagonal-source-endpoint-maps). -/
@[irreducible] def sourceEndpointRight
    (s : q.quotientRight ≅ q.restriction ⋙ q.cyclicRight) : q.sourceEndpointHomType s :=
  endpointComponent% (endpointSquare l Y E π n A hA q) s 2

end UniformizerSquareData
end AlgebraicGeometry.ProEtale.DiagonalCoefficients
