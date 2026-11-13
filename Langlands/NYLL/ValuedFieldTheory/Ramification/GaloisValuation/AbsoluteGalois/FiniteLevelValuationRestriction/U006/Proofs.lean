/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/- Modifications by Worker 256, with proof guidance by Worker 122 (2026-11-13):
   extract M233.006 from upstream commit
   fbd320cd8b1b06487c58227e92eb135794267709,
   FiniteLevelValuationRestriction.lean lines 126-130. Prefix the namespace
   with Langlands.NYLL and prove the published closed target by introducing
   its telescope before the original Iff.rfl proof. Preserve @[simp]
   and replace upstream imports by the published Statements module.
   Original LICENSE and NOTICE are retained in licenses/NYLL/. -/

import Langlands.NYLL.ValuedFieldTheory.Ramification.GaloisValuation.AbsoluteGalois.FiniteLevelValuationRestriction.Statements

namespace Langlands.NYLL.RamificationTheory.ValuationSubring

universe u v

/-- M233.006: membership in a restriction is membership of the ambient image. -/
@[simp] theorem mem_restrictIntermediateField_iff :
    mem_restrictIntermediateField_iffStatement.{u, v} := by
  intro K Ω _ _ _ A E x
  exact Iff.rfl

end Langlands.NYLL.RamificationTheory.ValuationSubring
