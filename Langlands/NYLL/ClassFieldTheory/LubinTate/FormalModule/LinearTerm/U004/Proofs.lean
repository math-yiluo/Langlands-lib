/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
Modifications by Worker 464 (2026-11-14): extract this focused M347.004 proof
from the pinned source at fbd320cd8b1b06487c58227e92eb135794267709;
prefix its namespace by Langlands.NYLL, import its published Prop target,
prove that exact target, and compute the linear form's constant coefficient
locally. Adaptations are recorded in the paired Markdown. Retained license
and notices: licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.LinearTerm.Statements

/-!
# A series with a prescribed linear term has zero constant coefficient

Proof of NYLL M347.004 for the published target
`Langlands.NYLL.LubinTate.SameUniformizer.HasLinearTerm.constantCoeff_eq_zeroStatement`.
-/

namespace Langlands.NYLL.LubinTate.SameUniformizer

universe u v

variable {R : Type u} [CommRing R]
variable {σ : Type v} [Fintype σ]

namespace HasLinearTerm

variable {H : MvPowerSeries σ R} {L : σ → R}

/-- A series with a prescribed linear term has zero constant
coefficient. -/
theorem constantCoeff_eq_zero (h : HasLinearTerm H L) :
    constantCoeff_eq_zeroStatement h := by
  change MvPowerSeries.constantCoeff H = 0
  have horder : (1 : ℕ∞) ≤ (H - linearForm L).order :=
    (by norm_num : (1 : ℕ∞) ≤ 2).trans h
  have hconstant :=
    MvPowerSeries.one_le_order_iff_constCoeff_eq_zero.mp horder
  have hlinear : MvPowerSeries.constantCoeff (linearForm L) = 0 := by
    simp [linearForm]
  simpa [hlinear] using hconstant

end HasLinearTerm

end Langlands.NYLL.LubinTate.SameUniformizer
