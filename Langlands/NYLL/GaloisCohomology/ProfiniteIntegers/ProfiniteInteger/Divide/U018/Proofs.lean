/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.Divide.Statements

/-!
# NYLL M009.018: division after multiplication

Modified by Worker 356: extract M009.018 from the pinned NYLL
ProfiniteInteger source, add the Langlands.NYLL namespace prefix, import
the focused published target, and conclude that exact target proposition.
Retain the source inverse-law proof and omit the source simp attribute
because the theorem concludes an opaque target proposition. See the paired
Markdown and licenses/NYLL/LICENSE and NOTICE.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

/-- Division of the canonical range element `n • x` recovers `x`. -/
theorem zHatDivide_zHatMulNat (n : ℕ) (hn : 0 < n) (x : ZHat) :
    zHatDivide_zHatMulNatStatement n hn x := by
  change (zHatMulNatRangeEquiv n hn).symm
    ((zHatMulNatRangeEquiv n hn) x) = x
  exact (zHatMulNatRangeEquiv n hn).symm_apply_apply x

end
end Langlands.NYLL.ClassFormation
