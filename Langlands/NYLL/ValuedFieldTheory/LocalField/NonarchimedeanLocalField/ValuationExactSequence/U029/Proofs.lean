/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExactSequence.KernelStatements
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExactSequence.U004.Proofs
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExactSequence.U028.Proofs
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic.U019.Proofs

/-!
# Integer units are exactly the valuation kernel

Modified by Worker 290, 16 November 2026: extract the proof of M134.029
from `Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ValuationExactSequence.lean`
at fbd320cd8b1b06487c58227e92eb135794267709; prefix the namespace with
`Langlands.NYLL`, import the focused published target and the three proof
dependencies, and state the theorem as the published closed proposition.
Introduce its full telescope before the unchanged source proof. The
reconstruction specification M134.028 is reused from the Library, with no
local copy. Omit the unused source noncomputable section and all other
source declarations. See the paired Markdown and `licenses/NYLL/LICENSE`
and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField

open scoped ValuativeRel WithZero

/-- A field unit comes from a valuation-ring unit exactly when its additive valuation is zero. -/
theorem integerUnitsToFieldUnits_mem_range_iff_valuationMap_eq_zero.{u} :
    integerUnitsToFieldUnits_mem_range_iff_valuationMap_eq_zeroStatement.{u} := by
  intro K _ _ _ _ x
  constructor
  · rintro ⟨u, rfl⟩
    rw [valuationMap_apply]
    exact v_integerUnitsToFieldUnits K u
  · intro hx
    exact ⟨integerUnitOfValuationMapZero K x hx,
      integerUnitOfValuationMapZero_spec K x hx⟩

end Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField
