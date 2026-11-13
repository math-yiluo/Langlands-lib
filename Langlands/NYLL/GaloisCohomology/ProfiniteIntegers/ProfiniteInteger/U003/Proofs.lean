/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.Statements

/-!
# Evaluation of natural multiplication on the NYLL profinite integers

Modified by Worker 238: extract M009.003 from the pinned NYLL source,
prefix the namespace with Langlands.NYLL, and give the theorem the exact
published Statement type. Retain the source parameters, simp attribute and
reflexivity proof. See the paired Markdown and licenses/NYLL/LICENSE and NOTICE.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

/-- The defining evaluation formula for natural multiplication. -/
@[simp]
theorem zHatMulNat_apply (n : ℕ) (x : ZHat) :
    zHatMulNat_applyStatement n x :=
  rfl

end
end Langlands.NYLL.ClassFormation
