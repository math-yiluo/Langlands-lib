/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.Divide.Statements

/-!
# NYLL M009.017: multiplication after division

Modified by Worker 356: extract M009.017 from the pinned NYLL
ProfiniteInteger source, add the Langlands.NYLL namespace prefix, import
the focused published target, and conclude that exact target proposition.
Retain the source inverse-law proof and omit the source simp attribute
because the theorem concludes an opaque target proposition. See the paired
Markdown and licenses/NYLL/LICENSE and NOTICE.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

/-- Multiplication by `n` recovers the underlying element of its range. -/
theorem zHatMulNat_zHatDivide (n : ℕ) (hn : 0 < n)
    (y : (zHatMulNat n).toAddMonoidHom.range) :
    zHatMulNat_zHatDivideStatement n hn y := by
  change ((zHatMulNatRangeEquiv n hn)
    ((zHatMulNatRangeEquiv n hn).symm y)).1 = y.1
  exact congrArg Subtype.val ((zHatMulNatRangeEquiv n hn).apply_symm_apply y)

end
end Langlands.NYLL.ClassFormation
