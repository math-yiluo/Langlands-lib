/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

-- Adapted by Worker 315 from NYLL commit fbd320cd8b1b06487c58227e92eb135794267709,
-- Conductor.lean, lines 34–39 (M290.001), as a Prop-valued statement target.
-- The namespace is prefixed, imports are focused, and the source proof is omitted.
-- See Statements.md and licenses/NYLL/ for the complete modification record.

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.StandardOpenSubgroups.Definitions

/-!
# Field principal-unit antitonicity: statement target

The full type of NYLL's `LocalClassFieldTheory.fieldPrincipalUnits_antitone`
is retained as a proposition about the published principal-unit filtration.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

/-- The field-level principal-unit filtration is antitone in its exponent. -/
def fieldPrincipalUnits_antitoneStatement : Prop :=
  ∀ (K : Type) [Field K] [ValuativeRel K] {m n : ℕ},
    m ≤ n →
      Langlands.NYLL.LocalFieldTheory.fieldPrincipalUnits K n ≤
        Langlands.NYLL.LocalFieldTheory.fieldPrincipalUnits K m

end Langlands.NYLL.LocalClassFieldTheory
