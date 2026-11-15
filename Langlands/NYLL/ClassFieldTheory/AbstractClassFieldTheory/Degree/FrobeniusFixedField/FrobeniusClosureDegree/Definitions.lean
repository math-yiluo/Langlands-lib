/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusFixedField.FrobeniusClosure.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusFixedField.NormalizedDegreeContinuous.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusFixedField.U003.Definitions

/-!
# The normalized degree restricted to the Frobenius closure

Modified by Worker 5264, 15 November 2026: extract M014.028
`frobeniusClosureDegree` from
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/FrobeniusFixedField.lean`
at fbd320cd8b1b06487c58227e92eb135794267709, prefixing the namespace with
`Langlands.NYLL`. The source-private helper `continuousSubgroupSubtype` is
replaced by its published adaptation `Langlands.NYLL.PortInternal.M014.d003`
(M014.003). As in the published sibling modules,
`extensionSubgroup K.field L hLK` is expanded to its exact Mathlib body
`L.toSubgroup.subgroupOf K.field.toSubgroup`. The source imports are
replaced by focused published imports. The source universe and variable
declarations, docstring, binders and the remaining body are retained. See
the paired Markdown and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- The normalized degree restricted to `Γ`. -/
def frobeniusClosureDegree (D : DegreeData G) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK) :
    D.frobeniusClosure K L hLK σ →ₜ* ZHatMul :=
  (D.extensionNormalizedDegreeContinuous K L hLK).comp
    (Langlands.NYLL.PortInternal.M014.d003
      (D.frobeniusClosure K L hLK σ).toSubgroup)

end DegreeData

end
end Langlands.NYLL.ClassFormation
