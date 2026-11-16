/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.NormSubgroup.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusLift.Definitions

/-!
# Targets: the subgroup of the maximal unramified field inside `G_K`

Modified by Worker 5264, 15 November 2026: extract the statements of M029.022
and M029.023 from
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/NormSubgroup.lean`
at fbd320cd8b1b06487c58227e92eb135794267709, prefix the namespace with
`Langlands.NYLL`, and replace the source imports by the published
maximal-unramified-field and relative-inertia definitions modules. Replace
each source theorem by a Prop-valued definition with the `Statement` suffix,
omitting its proof, and reword the declaration docstrings to describe the
propositions. Both propositions mention the containment proof
`D.maximalUnramifiedField_le_of_le hLK` (M029.020), whose proof is not
published: it is replaced by the source proof of that theorem,
`(D.maximalUnramifiedField_le L).trans hLK`, with M029.019
`maximalUnramifiedField_le` (also unpublished) replaced by the final step
`inf_le_left` of its source proof, stated with `show`. That source proof first
rewrites with M029.017 `maximalUnramifiedField_eq_fieldInertia`, a `rfl`
theorem; here the goal is checked by definitional unfolding instead
(`D.maximalUnramifiedField L` is `D.fieldInertia L`, which is
`L ⊓ D.inertia`). By proof irrelevance the propositions are unchanged. The second target is
preceded by `set_option linter.unusedVariables false in`, which keeps the
source name of the normality binder that the proposition does not mention.
Omit the opens, sections and declarations of the source file that these
targets do not use. See the paired Markdown and `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

universe u

namespace Langlands.NYLL.ClassFormation

open CyclicCohomology

noncomputable section

section maximalUnramifiedFields

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- The proposition, from the source theorem
`extensionSubgroup_maximalUnramifiedField`, that inside `G_K` the absolute
subgroup of the maximal unramified field `\widetilde L` is the relative
inertia subgroup. -/
def extensionSubgroup_maximalUnramifiedFieldStatement (D : DegreeData G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup) : Prop :=
    extensionSubgroup K (D.maximalUnramifiedField L)
        ((show (D.maximalUnramifiedField L).toSubgroup ≤ L.toSubgroup from
          inf_le_left).trans hLK) =
      D.extensionInertiaWithin K L hLK

set_option linter.unusedVariables false in
/-- The proposition, from the source theorem
`extensionSubgroup_maximalUnramifiedField_normal`, that the subgroup
representing the maximal unramified field is normal in the base subgroup
when the subgroup of `L` is. -/
def extensionSubgroup_maximalUnramifiedField_normalStatement (D : DegreeData G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L hLK).Normal] : Prop :=
    (extensionSubgroup K (D.maximalUnramifiedField L)
      ((show (D.maximalUnramifiedField L).toSubgroup ≤ L.toSubgroup from
        inf_le_left).trans hLK)).Normal

end DegreeData

end maximalUnramifiedFields

end
end Langlands.NYLL.ClassFormation
