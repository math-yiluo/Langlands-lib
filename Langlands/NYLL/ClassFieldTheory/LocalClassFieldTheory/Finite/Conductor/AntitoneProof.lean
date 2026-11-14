/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

-- Adapted by Worker 322 from NYLL commit fbd320cd8b1b06487c58227e92eb135794267709,
-- Conductor.lean, lines 34–39 (M290.001), inlining the integer-ring argument
-- from PrincipalUnits.lean, lines 79–84 (M131.005).
-- See AntitoneProof.md and licenses/NYLL/ for source correspondence and modifications.

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.Conductor.Statements

/-!
# Field principal-unit antitonicity

The field-unit filtration decreases because maximal-ideal powers decrease
and subgroup images preserve inclusion.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

/-- The field-level principal-unit filtration is antitone in its exponent. -/
theorem fieldPrincipalUnits_antitone : fieldPrincipalUnits_antitoneStatement := by
  intro K _ _ m n hmn
  apply Subgroup.map_mono
  intro u hu
  exact Ideal.pow_le_pow_right hmn hu

end Langlands.NYLL.LocalClassFieldTheory
