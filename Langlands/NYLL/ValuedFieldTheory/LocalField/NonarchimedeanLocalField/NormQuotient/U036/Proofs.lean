/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 1560, 5 November 2026 UTC:
Extract only the proof of M093.036 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix and import only the published U036 Statements module.
Prove its closed proposition by introducing all nine internal binders
before retaining the original rewrite by h and normClass_normUnits_mul.
Preserve shared universe u, implicit representatives x and y, explicit
extension unit z and named h with the actual unit norm as the left factor.
Omit the original noncomputable section, unused universe v and other units.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U036.Statements

/-!
# Equal norm classes from left multiplication by a unit norm

The exact proof of the published closed assertion: if one base-field unit
equals an extension-unit norm times another, their norm classes agree.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u

/-- A representative obtained by multiplying another by a unit norm defines the same norm class. -/
theorem normClass_eq_of_eq_normUnits_mul : NormClassEqOfEqNormUnitsMulStatement.{u} := by
  intro K L _ _ _ x y z h
  rw [h, normClass_normUnits_mul]

end Langlands.NYLL.LocalFieldTheory
