/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.Definitions

/-!
# Target: conjugation preserves inclusions of abstract fields

Modified by Worker 5264, 15 November 2026: state the source theorem M035.001
`conjugateClosedSubgroup_mono` of
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/NormConjugation.lean`
at fbd320cd8b1b06487c58227e92eb135794267709 as a Prop-valued Statement
definition. Prefix the namespace with `Langlands.NYLL`, append `Statement`
to the name, replace the source imports by a focused published import, keep
the source universe and variable declarations, the section `GroupOnly`,
parameters and binder kinds, omit the proof, the unused opens and the rest of
the source file, and turn off the unused-variable linter for the hypothesis
`hLK`, which the proposition does not mention. See the paired Markdown and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

universe u

section GroupOnly

variable {G : Type u} [Group G] [TopologicalSpace G]

set_option linter.unusedVariables false in
/-- Target: conjugation preserves inclusions of abstract fields. -/
def conjugateClosedSubgroup_monoStatement [ContinuousMul G]
    {K L : ClosedSubgroup G} (hLK : L.toSubgroup ≤ K.toSubgroup)
    (s : G) : Prop :=
    (conjugateClosedSubgroup L s).toSubgroup ≤
      (conjugateClosedSubgroup K s).toSubgroup

end GroupOnly

end

end Langlands.NYLL.ClassFormation
