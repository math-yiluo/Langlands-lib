/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.Statements

/-!
# Closedness of the natural multiplication image on the NYLL profinite integers

Modified by Worker 106: prove the published target M009.006,
`isClosed_zHatMulNat_rangeStatement`, with the source proof of
`ClassFormation.isClosed_zHatMulNat_range` (pinned NYLL ProfiniteInteger
source lines 104–108). Prefix the namespace with `Langlands.NYLL`, state the
theorem as the published target applied to `n`, and unfold that target before
the retained source tactics. Replace the source imports by the published target
module. See the paired Markdown and licenses/NYLL/LICENSE and NOTICE.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

/-- The image `n ℤ̂` is closed, for every natural number `n` including zero. -/
theorem isClosed_zHatMulNat_range (n : ℕ) :
    isClosed_zHatMulNat_rangeStatement n := by
  unfold isClosed_zHatMulNat_rangeStatement
  rw [AddMonoidHom.coe_range]
  exact (isCompact_range (map_continuous (zHatMulNat n))).isClosed

end
end Langlands.NYLL.ClassFormation
