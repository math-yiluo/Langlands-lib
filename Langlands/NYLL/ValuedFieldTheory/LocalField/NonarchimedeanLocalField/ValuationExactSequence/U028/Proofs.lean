/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 127, 15 November 2026:
Extract the proofs of M134.028 (lines 272-281), M134.039 (lines 435-445)
and M134.040 (lines 447-454) from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ValuationExactSequence.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix, import only the U028 Statements module, and prove each
published closed proposition by introducing its binders and then following
the source proof unchanged (`ext; rfl`, the source term, and the source
`rw`/`simp` pair; the source names inside the proofs now denote the closed
theorems of this file and the published M134.037 theorem). The
source `@[simp]` attributes of M134.028 and M134.039 are not put on the
closed theorems, where they would not give usable simp lemmas; the source
simp behavior is restored by two explicit-telescope `@[simp]` wrappers
derived from the exact closed theorems. Omit the source noncomputable
section and all other source declarations. The original LICENSE and NOTICE
are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExactSequence.U028.Statements

/-!
# Valuation-ring units from field units of valuation zero: proofs

The valuation-ring unit built from a field unit of valuation zero maps back
to that field unit, and the integer-unit factor in the decomposition
`x = u * ϖ ^ v(x)` has underlying field unit `x / ϖ ^ v(x)`.
-/

namespace Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField

universe u

open scoped ValuativeRel WithZero

/-- The valuation-ring unit reconstructed from a field unit of valuation zero maps back to that
field unit. -/
theorem integerUnitOfValuationMapZero_spec :
    integerUnitOfValuationMapZero_specStatement.{u} := by
  intro K _ _ _ _ x hx
  ext
  rfl

/-- Explicit-telescope simp form of `integerUnitOfValuationMapZero_spec`. -/
@[simp]
theorem integerUnitOfValuationMapZero_spec_apply (K : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (x : Kˣ) (hx : valuationMap K (Additive.ofMul x) = 0) :
    integerUnitsToFieldUnits K (integerUnitOfValuationMapZero K x hx) = x :=
  integerUnitOfValuationMapZero_spec K x hx

/-- Removing the uniformizer power prescribed by a field unit's valuation leaves a valuation-ring
unit. -/
theorem integerUnitsToFieldUnits_uniformizerUnitFactor :
    integerUnitsToFieldUnits_uniformizerUnitFactorStatement.{u} := by
  intro K _ _ _ _ ϖ hϖ x
  exact integerUnitOfValuationMapZero_spec K
    (x / ϖ ^ valuationMap K (Additive.ofMul x))
    (uniformizerUnitFactorValuationZero K ϖ x hϖ)

/-- Explicit-telescope simp form of `integerUnitsToFieldUnits_uniformizerUnitFactor`. -/
@[simp]
theorem integerUnitsToFieldUnits_uniformizerUnitFactor_apply (K : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (ϖ : Kˣ) (hϖ : valuationMap K (Additive.ofMul ϖ) = 1) (x : Kˣ) :
    integerUnitsToFieldUnits K (uniformizerUnitFactor K ϖ hϖ x) =
      x / ϖ ^ valuationMap K (Additive.ofMul x) :=
  integerUnitsToFieldUnits_uniformizerUnitFactor K ϖ hϖ x

/-- Standard local-field unit/uniformizer decomposition in multiplicative form. -/
theorem uniformizerUnitFactor_mul_uniformizer_zpow :
    uniformizerUnitFactor_mul_uniformizer_zpowStatement.{u} := by
  intro K _ _ _ _ ϖ hϖ x
  rw [integerUnitsToFieldUnits_uniformizerUnitFactor]
  simp [div_eq_mul_inv, mul_assoc]

end Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField
