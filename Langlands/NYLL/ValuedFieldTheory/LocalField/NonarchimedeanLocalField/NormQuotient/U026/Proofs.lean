/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 248, 1 November 2026:
Extract only the proof of M093.026 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix and prove the published closed LocalNormSubgroupSelfStatement
by introducing its two internal binders, then retain the original
ext/constructor proof with the public normUnits_self_apply witness.
Import only U026.Statements and preserve its entire public chain.
Retain the sole universe u and canonical self-algebra; omit the original
noncomputable section, unused universe v and all other declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U026.Statements

/-!
# Norm subgroup for the identity extension

Proof of the closed assertion that every base-field unit is a norm for the
identity extension.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u

/-- For the identity extension, every base-field unit is a norm. -/
theorem localNormSubgroup_self : LocalNormSubgroupSelfStatement.{u} := by
  intro K _
  ext x
  constructor
  · intro _
    exact Subgroup.mem_top x
  · intro _
    exact ⟨x, normUnits_self_apply K x⟩

end Langlands.NYLL.LocalFieldTheory
