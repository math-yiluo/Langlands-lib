/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RepresentationTheory.Rep.Basic
import Langlands.NYLL.GaloisCohomology.Cyclic.IntegralRepUniverse

/-!
# NYLL abstract reciprocity: the fixed corrected combination

Modified by Worker 68, 13 November 2026: extract the asserted type of M084.001, lines
31–37 from
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/TotallyRamifiedCase/FixedSource.lean`
at `fbd320cd8b1b06487c58227e92eb135794267709` as a Prop-valued definition without its proof.
Prefix the namespace with `Langlands.NYLL`, append `Statement` to the theorem name and use
focused imports. See the paired Markdown for all changes and `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE` for retained attribution.
-/

noncomputable section

namespace Langlands.NYLL.ClassFormation

-- Preserve the source hypothesis names even when the conclusion does not mention them.
set_option linter.unusedVariables false in
/-- Target of `abstractReciprocity_fixedCombination_of_commute`: if two commuting group
elements act compatibly on a coboundary, the standard corrected combination is fixed by the
first element. -/
def abstractReciprocity_fixedCombination_of_commuteStatement
    {Q : IntegralRepGroupType} [Group Q] (B : Rep ℤ Q)
    (g t : Q) (hcomm : Commute g t) (c b a : B.V)
    (htc : B.ρ t c = c)
    (hgb : B.ρ g b = B.ρ t b)
    (hbc : b - c = B.ρ g a - a) : Prop :=
    B.ρ g (b + a - B.ρ t a) = b + a - B.ρ t a

end Langlands.NYLL.ClassFormation

end
