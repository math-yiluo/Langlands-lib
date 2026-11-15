/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.Definitions

/-!
# Target: conjugating an abstract field does not change its degree image

Modified by Worker 5264, 15 November 2026: state the source theorem M027.001
`DegreeData.fieldImage_conjugate` of
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/ValuationLaws.lean`
at fbd320cd8b1b06487c58227e92eb135794267709 as a Prop-valued Statement
definition. Prefix the namespace with `Langlands.NYLL`, append `Statement`
to the name, replace the source imports by a focused published import, keep
the parameters and binder kinds of the theorem, which binds its own `G`, and
omit the proof, the unused opens and variable declarations and the rest of
the source file. See the paired Markdown and `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

/-- Target: conjugating an abstract field does not change its degree image. -/
def DegreeData.fieldImage_conjugateStatement
    {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G]
    (D : DegreeData G) (K : ClosedSubgroup G) (σ : G) : Prop :=
    D.fieldImage (conjugateClosedSubgroup K σ) = D.fieldImage K

end

end Langlands.NYLL.ClassFormation
