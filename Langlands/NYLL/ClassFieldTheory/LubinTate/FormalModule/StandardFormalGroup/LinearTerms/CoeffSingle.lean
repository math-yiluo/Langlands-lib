/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 497, 2026-11-14: port the proof of M354.002
(HasLinearTerm.coeff_single, source lines 66-74 of StandardFormalGroup.lean,
upstream commit fbd320cd8b1b06487c58227e92eb135794267709) as a proof of the
published target coeff_singleStatement, under the namespace prefix
Langlands.NYLL. The source step citing M354.001 is replaced by the same
order-bound argument inline, so this file does not depend on the M354.001
proof module.
The original LICENSE and NOTICE remain in licenses/NYLL/.

Prepared by Worker 338, 2026-11-16: reuse Worker 497's shared draft
revision 1 without changing the theorem or proof; complete the paired
Markdown extraction and adaptation record for focused submission.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.StandardFormalGroup.LinearTerms.Statements

/-!
# M354.002: the coefficient of a variable in a series with linear term

Proof of `HasLinearTerm.coeff_singleStatement`: the coefficient of `X_i` in a
series with prescribed linear term `L` is `L i`.
-/

universe w

namespace Langlands.NYLL.LubinTate
namespace SameUniformizer

variable {R : Type*} [CommRing R]
variable {σ : Type w} [Fintype σ]

namespace HasLinearTerm

/-- The coefficient of `X_i` is the prescribed coefficient `L i`
(NYLL M354.002). -/
theorem coeff_single
    {H : MvPowerSeries σ R} {L : σ → R}
    (hH : HasLinearTerm H L) (i : σ) :
    coeff_singleStatement hH i := by
  have hd : ((Finsupp.single i 1 : σ →₀ ℕ).degree : ℕ∞) < (2 : ℕ∞) := by
    rw [Finsupp.degree_single]
    norm_num
  have hzero :=
    MvPowerSeries.coeff_of_lt_order (hd.trans_le hH)
  rw [map_sub, sub_eq_zero] at hzero
  rw [coeff_singleStatement, hzero]
  classical
  simp [linearForm, MvPowerSeries.coeff_index_single_X]

end HasLinearTerm

end SameUniformizer
end Langlands.NYLL.LubinTate
