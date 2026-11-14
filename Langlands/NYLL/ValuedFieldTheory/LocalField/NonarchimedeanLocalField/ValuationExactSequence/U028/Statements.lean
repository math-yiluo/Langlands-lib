/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Adapted by Worker 85, 14 November 2026: extracted the types of the source
theorems LocalFieldTheory.IsNonarchimedeanLocalField.integerUnitOfValuationMapZero_spec
(inventory M134.028), integerUnitsToFieldUnits_uniformizerUnitFactor
(M134.039) and uniformizerUnitFactor_mul_uniformizer_zpow (M134.040). Each
complete source telescope is packaged as a closed Prop-valued definition
with the suffix Statement, in the namespace prefixed with Langlands.NYLL.
Proofs and the `@[simp]` attributes are omitted; the NYLL imports are
replaced by the published modules defining integerUnitsToFieldUnits,
integerUnitOfValuationMapZero and uniformizerUnitFactor. All other source declarations are omitted. The
retained license and notice are licenses/NYLL/LICENSE and
licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic.U016.Definitions
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExactSequence.U027.Definitions

/-!
# Valuation-ring units from field units of valuation zero: statement targets

Source: Naganori Yamaguchi, ClassFieldTheory, commit
fbd320cd8b1b06487c58227e92eb135794267709,
`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ValuationExactSequence.lean`,
lines 20–28 (namespaces, universe and opens), 272–280 (inventory M134.028),
435–445 (M134.039) and 447–454 (M134.040).

NYLL's `valuationMap` is the negative of the usual normalized order: a prime
element of `𝒪[K]` has value `-1`. A field unit `ϖ` with value `1` is
therefore an inverse uniformizer; the source names keep the word
"uniformizer".
-/

namespace Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField

open scoped ValuativeRel WithZero

/-- Statement target for source unit M134.028: the valuation-ring unit
`integerUnitOfValuationMapZero K x hx`, built from a field unit `x` whose
`valuationMap` value is zero, maps back to `x` under
`integerUnitsToFieldUnits K`. -/
def integerUnitOfValuationMapZero_specStatement.{u} : Prop :=
  ∀ (K : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (x : Kˣ) (hx : valuationMap K (Additive.ofMul x) = 0),
    integerUnitsToFieldUnits K (integerUnitOfValuationMapZero K x hx) = x

/-- Statement target for source unit M134.039: for a field unit `ϖ` whose
`valuationMap` value is one (an inverse uniformizer under NYLL's sign
convention), the field unit underlying `uniformizerUnitFactor K ϖ hϖ x` is
`x / ϖ ^ v(x)`, where `v(x)` is the `valuationMap` value of `x`. -/
def integerUnitsToFieldUnits_uniformizerUnitFactorStatement.{u} : Prop :=
  ∀ (K : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (ϖ : Kˣ) (hϖ : valuationMap K (Additive.ofMul ϖ) = 1) (x : Kˣ),
    integerUnitsToFieldUnits K (uniformizerUnitFactor K ϖ hϖ x) =
      x / ϖ ^ valuationMap K (Additive.ofMul x)

/-- Statement target for source unit M134.040: for a field unit `ϖ` whose
`valuationMap` value is one (an inverse uniformizer under NYLL's sign
convention), `x = u * ϖ ^ v(x)` with `u` the field unit underlying
`uniformizerUnitFactor K ϖ hϖ x`. -/
def uniformizerUnitFactor_mul_uniformizer_zpowStatement.{u} : Prop :=
  ∀ (K : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (ϖ : Kˣ) (hϖ : valuationMap K (Additive.ofMul ϖ) = 1) (x : Kˣ),
    integerUnitsToFieldUnits K (uniformizerUnitFactor K ϖ hϖ x) *
        ϖ ^ valuationMap K (Additive.ofMul x) = x

end Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField
