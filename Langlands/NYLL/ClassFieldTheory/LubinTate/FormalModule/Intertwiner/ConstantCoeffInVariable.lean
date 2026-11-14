/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 334, 2026-11-14: extract the proof M348.002 from
upstream commit fbd320cd8b1b06487c58227e92eb135794267709, import the
published focused statement module, prefix the namespace with Langlands.NYLL,
and state the theorem using its published proposition target. The proof,
binders and simp attribute are retained. Add focused documentation.
The original LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.Intertwiner.Statements

/-!
# Zero constant coefficient after insertion into a variable

Proof of the published M348.002 target for `inVariable`.
-/

noncomputable section

universe u v

namespace Langlands.NYLL.LubinTate
namespace SameUniformizer

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {π : F.valuationSubring}
variable {σ : Type*}

/-- The series `e(X_i)` has zero constant coefficient (NYLL M348.002). -/
@[simp]
theorem constantCoeff_inVariable (e : LubinTateSeries F π) (i : σ) :
    constantCoeff_inVariableStatement e i := by
  exact PowerSeries.constantCoeff_subst_eq_zero
    (MvPowerSeries.constantCoeff_X (R := F.valuationSubring) i)
    e.toPowerSeries e.constantCoeff_eq_zero

end SameUniformizer
end Langlands.NYLL.LubinTate

end
