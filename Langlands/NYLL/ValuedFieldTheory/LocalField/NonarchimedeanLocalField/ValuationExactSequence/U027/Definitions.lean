/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Adapted by Worker 85, 14 November 2026: extracted the source definitions
LocalFieldTheory.IsNonarchimedeanLocalField.integerUnitOfValuationMapZero
(inventory M134.027) and
LocalFieldTheory.IsNonarchimedeanLocalField.uniformizerUnitFactor (inventory
M134.038) under the same names in the namespace prefixed with Langlands.NYLL.
The binders, types and bodies are unchanged. The theorems named in the
bodies (valuation_integer_membership, M130.001;
valuation_eq_one_of_valuationMap_eq_zero, M134.020;
uniformizerUnitFactorValuationZero, M134.037) are their published
adaptations, whose types are closed Prop-valued statement definitions. The
NYLL imports are replaced by the published modules proving those three
theorems. All other source declarations are omitted. The retained license
and notice are licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Valuation.U001.Proofs
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExactSequence.U020.Proofs
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExactSequence.U037.Proofs

/-!
# Valuation-ring units from field units of valuation zero

Source: Naganori Yamaguchi, ClassFieldTheory, commit
fbd320cd8b1b06487c58227e92eb135794267709,
`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ValuationExactSequence.lean`,
lines 20–28 (namespace, universe and opens), 251–270 (inventory M134.027)
and 426–433 (inventory M134.038).
-/

namespace Langlands.NYLL.LocalFieldTheory

noncomputable section

universe u

namespace IsNonarchimedeanLocalField

open scoped ValuativeRel WithZero

/-- Defines `integerUnitOfValuationMapZero`. -/
def integerUnitOfValuationMapZero (K : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (x : Kˣ) (hx : valuationMap K (Additive.ofMul x) = 0) : 𝒪[K]ˣ where
  val := ⟨(x : K), by
    rw [valuation_integer_membership]
    have hv := valuation_eq_one_of_valuationMap_eq_zero K hx
    simp [hv]⟩
  inv := ⟨(x⁻¹ : K), by
    rw [valuation_integer_membership]
    have hv := valuation_eq_one_of_valuationMap_eq_zero K hx
    simp [hv]⟩
  val_inv := by
    apply Subtype.ext
    change (x : K) * (x : K)⁻¹ = 1
    exact mul_inv_cancel₀ x.ne_zero
  inv_val := by
    apply Subtype.ext
    change (x : K)⁻¹ * (x : K) = 1
    exact inv_mul_cancel₀ x.ne_zero

/-- The integer-unit factor in the standard decomposition `x = u * ϖ ^ v(x)`. -/
noncomputable def uniformizerUnitFactor (K : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (ϖ : Kˣ) (hϖ : valuationMap K (Additive.ofMul ϖ) = 1)
    (x : Kˣ) : 𝒪[K]ˣ :=
  integerUnitOfValuationMapZero K
    (x / ϖ ^ valuationMap K (Additive.ofMul x))
    (uniformizerUnitFactorValuationZero K ϖ x hϖ)

end IsNonarchimedeanLocalField

end

end Langlands.NYLL.LocalFieldTheory
