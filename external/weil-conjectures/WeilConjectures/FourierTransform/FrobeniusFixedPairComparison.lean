/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.FourierTransform.FdCoefficientComparisonSystem
public import WeilConjectures.DeligneLaumon.SfWeilSheafComplex
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcQbarCompletedPullback
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectCharacterization
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.Mathlib.Topology.KrullDimension
import WeilConjectures.Mathlib.CategoryTheory.Endofunctor.Algebra
import Mathlib.CategoryTheory.Equivalence

/-! # Frobenius fixed-pair comparison for a supplied comparison system

Source: blueprint main-20261015, sec-fourier-transform/sk-def-trace,
`def-fd-trace-function.md`, final sentence, geometric-fibre and fixed-pair auxiliary
(blueprint: lem-fd-frobenius-fixed-pair-comparison).

The finite/common-stage transports and scalar/inclusion comparisons below use the
specified comparisons of the supplied system, with their recorded reverse orientation.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u w u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme
open CategoryTheory.Endofunctor

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  (S : FdCoefficientComparisonSystem.{u} l Ω)
  (T : Scheme.{u}) [IsNoetherian T]
  [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
  [Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
  (g : T ≅ T)

private theorem cast_heq {α β : Sort u₁} (h : α = β) (x : α) : HEq x (cast h x) := by
  subst β
  rfl

set_option allowUnsafeReducibility true in
attribute [local reducible] StageSystem.Morphism.functor
  StageSystem.ι GeneralAlgebraicallyClosedCoefficients.stageCategory

set_option allowUnsafeReducibility true in
attribute [local irreducible] ScalarLocalization.category ScalarLocalization.preadditive
  ScalarLocalization.linear sfIntegralConstructible sfIntegralConstructibleLinear
  rationalDerivedPullback commonStageDerivedPullback integralDerivedPullback
  sfRationalScalarExtension Padic.coefficientExtensionIntegers
  Padic.coefficientExtensionUniformizer Padic.coefficientExtensionAbsoluteValue
  HasDerivedCategory.standard integralCoefficientLinear pbcQbarPullFamily

attribute [local implicit_reducible] GeneralAlgebraicallyClosedCoefficients.Stage
set_option linter.auxLemma false in
set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_1
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_3
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_5
set_option allowUnsafeReducibility true in
attribute [local irreducible] GeneralAlgebraicallyClosedCoefficients.stageSystem

end WeilConjectures
