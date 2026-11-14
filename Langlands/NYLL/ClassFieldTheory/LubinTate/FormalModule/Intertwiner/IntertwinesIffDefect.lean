/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 334, 2026-11-14: extract M348.006 from upstream commit
fbd320cd8b1b06487c58227e92eb135794267709, import the published focused
statement module, prefix the namespace with Langlands.NYLL, and express its
type through the published target. Explicitly unfold that reducible target
before the unchanged source simplification. Add focused documentation.
The original LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.Intertwiner.Statements

/-!
# Intertwining is equivalent to vanishing of the defect

Proof of the published M348.006 target.
-/

noncomputable section

universe u v

namespace Langlands.NYLL.LubinTate
namespace SameUniformizer

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {π : F.valuationSubring}
variable {σ : Type*}

/-- The intertwining equation holds exactly when its defect vanishes
(NYLL M348.006). -/
theorem intertwines_iff_defect_eq_zero
    (e ebar : LubinTateSeries F π)
    (H : MvPowerSeries σ F.valuationSubring) :
    intertwines_iff_defect_eq_zeroStatement e ebar H := by
  simp only [intertwines_iff_defect_eq_zeroStatement, Intertwines, defect, sub_eq_zero]

end SameUniformizer
end Langlands.NYLL.LubinTate

end
