/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 120, 13 November 2026:
Extract the proof of M134.004 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ValuationExactSequence.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix, import only the ValuationExactSequence
EvaluationStatements module, and prove the published closed proposition by
introducing its six binders before the original `rfl`. Keep the source
docstring's sentence once instead of twice. Omit the theorem-only `simp`
attribute, the source noncomputable section and all other source
declarations. The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExactSequence.EvaluationStatements

/-!
# Evaluation of the bundled valuation map

The bundled additive valuation map evaluates a field unit by the normalized
integer valuation.
-/

namespace Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField

universe u

open scoped ValuativeRel WithZero

/-- The additive valuation map evaluates a field unit by applying the normalized integer
valuation. -/
theorem valuationMap_apply : valuationMap_applyStatement.{u} := by
  intro K _ _ _ _ x
  rfl

end Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField
