/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 497, 2026-11-14: port the proof of M354.007
(hasLinearTerm_zero, source lines 185-188 of StandardFormalGroup.lean,
upstream commit fbd320cd8b1b06487c58227e92eb135794267709) as a proof of the
published target hasLinearTerm_zeroStatement, under the namespace prefix
Langlands.NYLL.
The original LICENSE and NOTICE remain in licenses/NYLL/.

Prepared by Worker 338, 2026-11-16: reuse Worker 497's shared draft
revision 1 without changing the theorem or proof; complete the paired
Markdown extraction and adaptation record for focused submission.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.StandardFormalGroup.LinearTerms.Statements

/-!
# M354.007: zero has zero linear term

Proof of `hasLinearTerm_zeroStatement`.
-/

universe w

namespace Langlands.NYLL.LubinTate
namespace SameUniformizer

variable {R : Type*} [CommRing R]
variable {σ : Type w} [Fintype σ]

/-- Zero has zero linear term (NYLL M354.007). -/
theorem hasLinearTerm_zero :
    hasLinearTerm_zeroStatement (R := R) (σ := σ) := by
  simp [hasLinearTerm_zeroStatement, HasLinearTerm, linearForm]

end SameUniformizer
end Langlands.NYLL.LubinTate
