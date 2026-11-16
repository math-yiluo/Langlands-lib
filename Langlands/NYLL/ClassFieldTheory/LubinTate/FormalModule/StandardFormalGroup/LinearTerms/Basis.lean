/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 497, 2026-11-14: port the proof of the private
source theorem LubinTate.SameUniformizer.linearForm_basis (M354.005, source
lines 171-176 of StandardFormalGroup.lean, upstream commit
fbd320cd8b1b06487c58227e92eb135794267709) as the public theorem
Langlands.NYLL.PortInternal.M354.d005 proving the published target
d005Statement.
The original LICENSE and NOTICE remain in licenses/NYLL/.

Prepared by Worker 338, 2026-11-16: reuse Worker 497's shared draft
revision 1 without changing the theorem or proof; complete the paired
Markdown extraction and adaptation record for focused submission.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.StandardFormalGroup.LinearTerms.Statements

/-!
# M354.005: the standard-basis linear form is a variable

Proof of `Langlands.NYLL.PortInternal.M354.d005Statement`.
-/

universe w

namespace Langlands.NYLL.PortInternal.M354

open Langlands.NYLL.LubinTate.SameUniformizer

variable {R : Type*} [CommRing R]
variable {σ : Type w} [Fintype σ]

/-- The linear form of the `i`-th standard basis vector is `X i`
(NYLL M354.005, private in the source). -/
theorem d005 (i : σ) : d005Statement (R := R) i := by
  classical
  simp [d005Statement, linearForm]

end Langlands.NYLL.PortInternal.M354
