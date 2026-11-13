/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/- Modifications by Worker 256, with proof guidance by Worker 122 (2026-11-13):
   extract M233.005 from upstream commit
   fbd320cd8b1b06487c58227e92eb135794267709,
   FiniteLevelValuationRestriction.lean lines 120-124. Prefix the namespace
   with Langlands.NYLL and prove the published closed target by introducing
   its telescope before the original reflexivity proof. Preserve @[simp]
   and replace upstream imports by the published Statements module.
   Original LICENSE and NOTICE are retained in licenses/NYLL/. -/

import Langlands.NYLL.ValuedFieldTheory.Ramification.GaloisValuation.AbsoluteGalois.FiniteLevelValuationRestriction.Statements

namespace Langlands.NYLL.RamificationTheory.ValuationSubring

universe u v

/-- M233.005: restricting a valuation subring is the comap along the inclusion. -/
@[simp] theorem restrictIntermediateField_eq_comap :
    restrictIntermediateField_eq_comapStatement.{u, v} := by
  intro K Ω _ _ _ A E
  rfl

end Langlands.NYLL.RamificationTheory.ValuationSubring
