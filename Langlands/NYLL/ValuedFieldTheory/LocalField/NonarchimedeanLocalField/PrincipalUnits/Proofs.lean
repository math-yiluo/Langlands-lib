/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

-- Adapted by Worker 229 from NYLL commit fbd320cd8b1b06487c58227e92eb135794267709,
-- PrincipalUnits.lean, lines 54–57 and 73–76: the theorem types are the published
-- closed targets, and the source proof bodies are retained. See Proofs.md and
-- licenses/NYLL/.

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnits.Statements

/-!
# Principal-unit membership and the zeroth subgroup: proofs

Membership in `principalUnits K n` is definitionally the ideal-membership
condition on its carrier, and the zeroth ideal power is the top ideal.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u

open scoped ValuativeRel

/-- A valuation-ring unit lies in the `n`-th principal-unit group exactly when it is congruent to
one modulo the `n`-th maximal-ideal power. -/
theorem mem_principalUnits_iff : MemPrincipalUnitsIffStatement.{u} :=
  fun _ _ _ _ _ => Iff.rfl

/-- The zeroth principal-unit group is the full unit group of the valuation ring. -/
theorem principalUnits_zero : PrincipalUnitsZeroStatement.{u} := by
  intro K _ _
  ext a
  simp [principalUnits]

end Langlands.NYLL.LocalFieldTheory
