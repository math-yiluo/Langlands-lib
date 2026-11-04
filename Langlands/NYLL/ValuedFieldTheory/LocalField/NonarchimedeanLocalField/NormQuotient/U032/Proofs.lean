/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 248, 3 November 2026:
Extract only the proof of M093.032 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix and import only the published U032 Statements module.
Prove its closed proposition by introducing the seven internal binders
before retaining the original map_mul, mk_normUnits_eq_one and one_mul proof.
Preserve the shared universe u, the extension unit z before the base unit x
and the left multiplication by the unit norm. Omit the original
noncomputable section, unused universe v and all other declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U032.Statements

/-!
# Left multiplication by a unit norm

The exact proof of the published closed assertion: multiplying a base-field
unit on the left by the unit norm of an extension-field unit leaves its norm
class unchanged.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u

/-- Multiplying a representative on the left by a unit norm leaves its norm class unchanged. -/
theorem normClass_normUnits_mul : NormClassNormUnitsMulStatement.{u} := by
  intro K L _ _ _ z x
  rw [map_mul, mk_normUnits_eq_one]
  exact one_mul (normClass K L x)

end Langlands.NYLL.LocalFieldTheory
