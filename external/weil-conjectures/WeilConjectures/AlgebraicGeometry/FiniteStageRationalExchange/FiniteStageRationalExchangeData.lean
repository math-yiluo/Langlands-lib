/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Ambient.AmbientCompleteCoefficientCategories
public import WeilConjectures.SmoothBaseChange.ECoefficientSmoothBaseChange
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarExtension
public import WeilConjectures.SmoothBaseChange.SbcCompletedOperations
public import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.CategoryTheory.StageSystem.Functor
public import WeilConjectures.CategoryTheory.StageSystem.StageSystemFunctorDescent

/-! # Data for finite-stage rational exchange coherence

These are the unchanged raw operations and coherence predicates used by
`FiniteStageRationalExchangeCoherence`. The raw-only predicate isolates the
coefficient construction before the supported Karoubi extension.
(blueprint: def-sbc-finite-stage-rational-exchange-data)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures TensorProduct

namespace AlgebraicGeometry.Scheme.FiniteStageRationalExchange

variable (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω]
  [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- The raw extension of the actual integral completed pullback.
Source: sketch32, lines 1218--1228
(blueprint: lem-sbc-finite-stage-rational-exchange-coherence). -/
abbrev rawPull (E : Padic.FiniteCoefficientFields l Ω)
    {U V : Scheme.{u}} (q : U ⟶ V) :=
  ScalarLocalization.between (PbcIntegralRing l (pbcFiniteField.{u} l Ω E))
    (pbcUniformizer l (pbcFiniteField.{u} l Ω E))
    (sbcPull l (pbcFiniteField.{u} l Ω E) q)

section Operations

variable {U V : Scheme.{u}} [IsNoetherian U] [IsNoetherian V]
  [dU : Fact (∃ n : ℕ, topologicalKrullDim U ≤ n)]
  [dV : Fact (∃ n : ℕ, topologicalKrullDim V ≤ n)]
  [iU : Fact (∀ x : U, IsUnit (l : U.presheaf.stalk x))]
  [iV : Fact (∀ x : V, IsUnit (l : V.presheaf.stalk x))]
  (q : U ⟶ V)

end Operations

section Square

variable {X S T Y : Scheme.{u}} {f : X ⟶ S} {g : T ⟶ S} {h : Y ⟶ X} {e : Y ⟶ T}
  [IsNoetherian X] [IsNoetherian S] [IsNoetherian T] [IsNoetherian Y]
  [dX : Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
  [dS : Fact (∃ n : ℕ, topologicalKrullDim S ≤ n)]
  [dT : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
  [dY : Fact (∃ n : ℕ, topologicalKrullDim Y ≤ n)]
  [iX : Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
  [iS : Fact (∀ x : S, IsUnit (l : S.presheaf.stalk x))]
  [iT : Fact (∀ x : T, IsUnit (l : T.presheaf.stalk x))]
  [iY : Fact (∀ x : Y, IsUnit (l : Y.presheaf.stalk x))]
  (sq : ChosenCartesianSquare h e f g)

end Square

end AlgebraicGeometry.Scheme.FiniteStageRationalExchange
