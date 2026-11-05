/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 1560, 5 November 2026 UTC:
Extract only the proof of M093.034 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix and import only the published U034 Statements module.
Prove its closed proposition by introducing the eight internal binders,
then retain the original map_mul, normClass_normUnits_zpow_eq_one and
one_mul proof. Preserve shared universe u, the integer exponent and left
multiplication by the powered actual unit norm. Omit the original
noncomputable section, unused universe v and all other declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U034.Statements

/-!
# Left multiplication by an integer power of a unit norm

The exact proof of the published closed assertion: multiplying a base-field
unit on the left by an integer power of an extension-field unit norm leaves
its norm class unchanged.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u

/-- Left multiplication by an integral power of a unit norm leaves a norm class unchanged. -/
theorem normClass_normUnits_zpow_mul : NormClassNormUnitsZpowMulStatement.{u} := by
  intro K L _ _ _ z n x
  rw [map_mul, normClass_normUnits_zpow_eq_one K L z n]
  exact one_mul (normClass K L x)

end Langlands.NYLL.LocalFieldTheory
