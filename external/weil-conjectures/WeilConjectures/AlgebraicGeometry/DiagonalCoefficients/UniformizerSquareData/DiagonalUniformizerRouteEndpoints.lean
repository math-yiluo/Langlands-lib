/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.UniformizerSquareData.DiagonalCoefficientRouteData

/-! # Successive finite coefficient route endpoints

Source: diagonal tower coefficient changes (1), derived adjunction transitivity.
(blueprint: def-diagonal-uniformizer-route-endpoints).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

-- Use the module-sheaf abelian structure of GeoCartierClass.
attribute [local instance 100000] sheafIsAbelian
attribute [local instance 200000] AlgebraicGeometry.ProEtale.diagonalAbSheafAbelian
attribute [local instance 300000] CommRing.toRing
attribute [local instance 400000] AlgebraicGeometry.ProEtale.diagonalModuleSheafAbelian
namespace UniformizerSquareData

variable {l : ℕ} [Fact l.Prime] {Y : Scheme.{u}}
  {E : PadicAlgCl.FiniteIntermediateField l} {π : PadicAlgCl.integers l E} {n : ℕ}
  {A : Type (u + 1)} [CommRing A] {hA : ((l ^ (n + 1) : ℕ) : A) = 0}
  (q : UniformizerSquareData l Y E π n A hA)

attribute [local irreducible] derivedScalars quotientLine quotientLineMap cyclicLine cyclicLineMap
  Functor.leftDerivedFunctor Mod.derivedExtendMapDerivedCategoryAdjunction
  HasDerivedCategory.standard DerivedCategory.singleFunctors
  HomotopyCategory.singleFunctors DerivedCategory.singleFunctorIsoCompQ

-- Primitive projections reuse the category data stored in the bundle's type.
-- The resulting terms are checked by Lean's kernel.
local elab "routeField% " i:num d:term:max : term => do
  let e ← Lean.Elab.Term.elabTerm d none
  return Lean.mkProj ``FiniteRouteData i.getNat e

abbrev quotientFunctor := routeField% 0 (q.quotientEndpoints l Y E π n A hA)

/-- The successive integral and quotient source endpoint. -/
abbrev quotientSource := routeField% 1 (q.quotientEndpoints l Y E π n A hA)

/-- The successive integral and quotient target endpoint at degree two. -/
abbrev quotientTarget := routeField% 2 (q.quotientEndpoints l Y E π n A hA)

end UniformizerSquareData
end AlgebraicGeometry.ProEtale.DiagonalCoefficients
