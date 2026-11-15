/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusLift.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteResidue.Definitions

/-!
# Target: the relative inertia subgroup is closed

Modified by Worker 5264, 15 November 2026: state the source theorem M014.022
`extensionInertiaWithin_isClosed` of
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/FrobeniusFixedField.lean`
at fbd320cd8b1b06487c58227e92eb135794267709 as a Prop-valued Statement
definition. Prefix the namespace with `Langlands.NYLL`, append `Statement`
to the name, replace the source imports by focused published imports, keep
the source universe and variable declarations, parameters and binder kinds,
and omit the proof, the unused `open CyclicCohomology` and the rest of the
source file. See the paired Markdown and `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- Target: the extension's inertia subgroup is closed inside its base
subgroup. -/
def extensionInertiaWithin_isClosedStatement (D : DegreeData G)
    [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup) : Prop :=
    IsClosed (D.extensionInertiaWithin K.field L hLK : Set K.field.toSubgroup)

end DegreeData

end

end Langlands.NYLL.ClassFormation
