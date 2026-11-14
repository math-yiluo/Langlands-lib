/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 135, 14 November 2026:
Extract the proof of M135.001 (lines 24–31) from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/PrincipalUnitActions.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Prefix the namespace with
Langlands.NYLL and prove the published closed statement by introducing its
telescope before the unchanged source rewrite. Import only the target
statement module. Omit all other source declarations. See paired Markdown.
The upstream LICENSE and NOTICE are preserved in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitActions.MaximalIdealStatements

/-!
# Valuation-ring equivalences and the maximal ideal

The exact proof of NYLL M135.001.
-/

namespace Langlands.NYLL.LocalFieldTheory

open scoped ValuativeRel

/-- A ring equivalence of a valuation integer ring preserves the maximal ideal. -/
theorem integerRingEquiv_mem_maximalIdeal.{u} :
    integerRingEquiv_mem_maximalIdealStatement.{u} := by
  intro K _ _ e x
  rw [IsLocalRing.mem_maximalIdeal, map_mem_nonunits_iff e,
    ← IsLocalRing.mem_maximalIdeal]

end Langlands.NYLL.LocalFieldTheory
