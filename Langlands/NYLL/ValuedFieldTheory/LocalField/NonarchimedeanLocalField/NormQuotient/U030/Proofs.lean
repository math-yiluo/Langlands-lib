/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 107, 1 November 2026:
Extract the proof of M093.030 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix and prove the published closed statement by introducing
its seven internal binders, then following the original proof unchanged.
Import only U030 Statements and preserve its complete public chain.
Omit the source noncomputable section, unused universe v and other units.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U030.Statements

/-!
# Integer powers of unit norms have trivial norm class

Every integer power of an extension-field unit norm maps to the identity
under the canonical projection to the norm quotient.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u

/-- An integral power of a unit norm has trivial norm class. -/
theorem normClass_normUnits_zpow_eq_one : NormClassNormUnitsZpowEqOneStatement.{u} := by
  intro K L _ _ _ x n
  rw [map_zpow, mk_normUnits_eq_one, one_zpow]

end Langlands.NYLL.LocalFieldTheory
