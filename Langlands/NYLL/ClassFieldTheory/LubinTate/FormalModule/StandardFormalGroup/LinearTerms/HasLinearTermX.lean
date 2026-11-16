/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 497, 2026-11-14: port the proof of M354.006
(hasLinearTerm_X, source lines 178-183 of StandardFormalGroup.lean, upstream
commit fbd320cd8b1b06487c58227e92eb135794267709) as a proof of the published
target hasLinearTerm_XStatement, under the namespace prefix Langlands.NYLL.
The source step citing the private M354.005 lemma is replaced by the same
simp computation inline, so this file does not depend on the M354.005
proof module.
The original LICENSE and NOTICE remain in licenses/NYLL/.

Prepared by Worker 338, 2026-11-16: reuse Worker 497's shared draft
revision 1 without changing the theorem or proof; complete the paired
Markdown extraction and adaptation record for focused submission.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.StandardFormalGroup.LinearTerms.Statements

/-!
# M354.006: a variable has the standard-basis linear term

Proof of `hasLinearTerm_XStatement`.
-/

attribute [local instance] Classical.propDecidable

universe w

namespace Langlands.NYLL.LubinTate
namespace SameUniformizer

variable {R : Type*} [CommRing R]
variable {σ : Type w} [Fintype σ]

/-- A variable has the corresponding standard-basis linear term
(NYLL M354.006). -/
theorem hasLinearTerm_X (i : σ) : hasLinearTerm_XStatement (R := R) i := by
  have hbasis :
      linearForm (R := R) (fun j : σ => if j = i then (1 : R) else 0) =
        (MvPowerSeries.X i : MvPowerSeries σ R) := by
    classical
    simp [linearForm]
  rw [hasLinearTerm_XStatement, HasLinearTerm, hbasis, sub_self,
    MvPowerSeries.order_zero]
  exact le_top

end SameUniformizer
end Langlands.NYLL.LubinTate
