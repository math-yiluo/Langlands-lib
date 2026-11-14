/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 127, 14 November 2026:
Extract the proof of M134.037 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ValuationExactSequence.lean
(lines 419-423) at fbd320cd8b1b06487c58227e92eb135794267709. Add the
Langlands.NYLL namespace prefix, import only the ValuationExactSequence
KernelStatements module, and prove the published closed proposition by
introducing its eight binders. Since no proofs of valuationMap_ofMul_div
(M134.021) and valuationMap_ofMul_zpow (M134.022) are in the Library, the
two source rewrites by these wrappers are replaced by Mathlib's
Additive.ofMul and additive-homomorphism laws (ofMul_div, map_sub,
ofMul_zpow, map_zsmul, smul_eq_mul); the remaining source rewrites hϖ,
mul_one and sub_self are kept. Omit the source noncomputable section and all
other source declarations. The original LICENSE and NOTICE are retained in
licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExactSequence.KernelStatements

/-!
# The uniformizer-power quotient has valuation zero

Dividing a field unit by the power of a valuation-one unit indexed by its
normalized valuation gives a unit of normalized valuation zero.
-/

namespace Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField

universe u

open scoped ValuativeRel WithZero

/-- The quotient of a field unit by the corresponding power of a uniformizer has
normalized valuation zero. -/
theorem uniformizerUnitFactorValuationZero :
    uniformizerUnitFactorValuationZeroStatement.{u} := by
  intro K _ _ _ _ ϖ x hϖ
  rw [ofMul_div, map_sub, ofMul_zpow, map_zsmul, hϖ, smul_eq_mul, mul_one, sub_self]

end Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField
