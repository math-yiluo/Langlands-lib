/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 497, 2026-11-14: port the proof of M354.001
(HasLinearTerm.coeff_eq_linearForm, source lines 51-64 of
StandardFormalGroup.lean, upstream commit
fbd320cd8b1b06487c58227e92eb135794267709) as a proof of the published
target coeff_eq_linearFormStatement, under the namespace prefix
Langlands.NYLL.
The original LICENSE and NOTICE remain in licenses/NYLL/.

Prepared by Worker 338, 2026-11-16: reuse Worker 497's shared draft
revision 1 without changing the theorem or proof; complete the paired
Markdown extraction and adaptation record for focused submission.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.StandardFormalGroup.LinearTerms.Statements

/-!
# M354.001: low-degree coefficients of a series with prescribed linear term

Proof of `HasLinearTerm.coeff_eq_linearFormStatement`: in total degree less
than two, a series with prescribed linear term agrees coefficientwise with
that linear form.
-/

universe w

namespace Langlands.NYLL.LubinTate
namespace SameUniformizer

variable {R : Type*} [CommRing R]
variable {σ : Type w} [Fintype σ]

namespace HasLinearTerm

/-- In total degree less than two, a series with prescribed linear term
agrees coefficientwise with that linear form (NYLL M354.001). -/
theorem coeff_eq_linearForm
    {H : MvPowerSeries σ R} {L : σ → R}
    (hH : HasLinearTerm H L)
    (d : σ →₀ ℕ) (hd : d.degree < 2) :
    coeff_eq_linearFormStatement hH d hd := by
  have hd' : (d.degree : ℕ∞) < (2 : ℕ∞) := by
    exact_mod_cast hd
  have hzero :=
    MvPowerSeries.coeff_of_lt_order (hd'.trans_le hH)
  rw [map_sub, sub_eq_zero] at hzero
  exact hzero

end HasLinearTerm

end SameUniformizer
end Langlands.NYLL.LubinTate
