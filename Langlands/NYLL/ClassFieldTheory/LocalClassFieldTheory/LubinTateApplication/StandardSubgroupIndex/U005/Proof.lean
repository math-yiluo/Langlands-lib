/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 580, 14 November 2026, from NYLL commit
fbd320cd8b1b06487c58227e92eb135794267709:
extract M377.005 (StandardSubgroupIndex.lean:124–139), prefix its namespace
with Langlands.NYLL, and prove the published universe-polymorphic Statement
by introducing its complete internal telescope. Retain the source proof body.
Import only its published statement module. See Proof.md and licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.LubinTateApplication.StandardSubgroupIndex.U005.Statements

universe u

namespace Langlands.NYLL.LubinTate

/-- Containment and equal nonzero subgroup indices imply equality. -/
theorem subgroup_eq_of_le_of_index_eq_of_ne_zero :
    subgroup_eq_of_le_of_index_eq_of_ne_zeroStatement.{u} := by
  intro G _ H N hHN hindex hindex_ne
  let _ : H.FiniteIndex := ⟨hindex_ne⟩
  apply le_antisymm hHN
  by_contra hNH
  have hne : H ≠ N := by
    intro heq
    apply hNH
    rw [heq]
  have hstrict : H < N := lt_of_le_of_ne hHN hne
  have hi := Subgroup.index_strictAnti hstrict
  rw [hindex] at hi
  exact Nat.lt_irrefl _ hi

end Langlands.NYLL.LubinTate
