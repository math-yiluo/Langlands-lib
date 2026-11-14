/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 135, 14 November 2026:
Extract the proof of M130.001 (lines 28–34) from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/Valuation.lean at
fbd320cd8b1b06487c58227e92eb135794267709. Prefix the namespace with
Langlands.NYLL and prove the published closed statement by introducing its
telescope before the unchanged source term. Import only the target statement
module. Omit all other source declarations. See paired Markdown. The upstream
LICENSE and NOTICE are preserved in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Valuation.MembershipStatement

/-!
# Membership in the valuation ring

The exact proof of NYLL M130.001.
-/

namespace Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField

open scoped ValuativeRel

/-- An element belongs to the valuation ring exactly when its valuation is at most one. -/
theorem valuation_integer_membership.{u} :
    valuation_integer_membershipStatement.{u} := by
  intro K _ _ x
  exact (Valuation.mem_integer_iff (ValuativeRel.valuation K) x).symm

end Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField
