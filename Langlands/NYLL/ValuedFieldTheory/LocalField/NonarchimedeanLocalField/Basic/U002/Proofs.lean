/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 120, 13 November 2026:
Extract the proof of M128.002 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/Basic.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix, import only the Basic ValuationStatements module, and
prove the published closed proposition by introducing its six binders
before the original `rfl`. Omit the theorem-only `simp` attribute, the
source noncomputable section and all other source declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic.ValuationStatements

/-!
# Evaluation of the normalized valuation

The normalized valuation of a field unit is, by definition, the additive
exponent of its transported nonzero value.
-/

namespace Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField

universe u

open scoped ValuativeRel WithZero

/-- The normalized integer valuation is obtained by transporting the field valuation to
multiplicative integers and taking its additive exponent. -/
theorem v_apply : v_applyStatement.{u} := by
  intro K _ _ _ _ x
  rfl

end Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField
