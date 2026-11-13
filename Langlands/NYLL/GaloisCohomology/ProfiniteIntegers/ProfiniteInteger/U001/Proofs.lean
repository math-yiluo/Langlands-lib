/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.Statements

/-!
# Uniqueness of natural powers of the NYLL profinite-integer generator

Modified by Worker 236: extract M009.001 from the pinned NYLL source,
prefix its namespace with Langlands.NYLL, and give the theorem the exact
published Statement type. Retain the source proof and replace its imports
with the target module. See the paired Markdown and licenses/NYLL/LICENSE
and NOTICE.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

/-- Distinct natural powers of the canonical positive generator of `ZHat`
are distinct. -/
theorem proCIntegerOne_pow_nat_injective :
    proCIntegerOne_pow_nat_injectiveStatement := by
  intro a b hab
  let m := a + b + 1
  have hm : 0 < m := by simp [m]
  have ha : a < m := by omega
  have hb : b < m := by omega
  have habAdd := congrArg Multiplicative.toAdd hab
  have habAdd' : a • (1 : ZHat) = b • (1 : ZHat) := by
    simpa using habAdd
  have habRed := congrArg (fun z : ZHat => zHatReduction m hm z) habAdd'
  have hredOne : zHatReduction m hm (1 : ZHat) = 1 :=
    rfl
  change zHatReduction m hm (a • (1 : ZHat)) =
      zHatReduction m hm (b • (1 : ZHat)) at habRed
  rw [map_nsmul, map_nsmul, hredOne] at habRed
  have hval := congrArg ZMod.val habRed
  simpa [ZMod.val_natCast_of_lt ha, ZMod.val_natCast_of_lt hb] using hval

end
end Langlands.NYLL.ClassFormation
