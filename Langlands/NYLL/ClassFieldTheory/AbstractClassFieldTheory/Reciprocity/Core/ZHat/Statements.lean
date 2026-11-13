/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteIntegerCore.Definitions

/-!
# NYLL abstract reciprocity: a profinite-integer step

Modified by Worker 68, 13 November 2026: extract the asserted type of M075.028, lines
1159–1163 from `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Core.lean` at
`fbd320cd8b1b06487c58227e92eb135794267709` as a Prop-valued definition without its proof.
Prefix the namespace with `Langlands.NYLL`, append `Statement` to the theorem name and use a
focused import of the published `ZHat`. See the paired Markdown for all changes and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` for retained attribution.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

-- Preserve the source hypothesis names even when the conclusion does not mention them.
set_option linter.unusedVariables false in
/-- Target of `abstractReciprocity_zHat_nsmul_eq_natCast_forces_zero`: an elementary
profinite-integer step, if `n z = k` in `ℤ̂`, with `0 ≤ k < n`, then `k = 0`. -/
def abstractReciprocity_zHat_nsmul_eq_natCast_forces_zeroStatement
    (n k : ℕ) (hn : 0 < n) (hk : k < n) (z : ZHat)
    (h : n • z =
      Int.castRingHom ZHat (k : ℤ)) : Prop :=
    k = 0

end
end Langlands.NYLL.ClassFormation
