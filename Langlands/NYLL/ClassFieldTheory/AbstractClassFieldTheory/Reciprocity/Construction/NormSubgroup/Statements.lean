/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.NormSubgroup.Definitions

/-!
# NYLL M029.017–021: targets for the maximal unramified field

Modified by Worker 483: extract the signatures of M029.017–021 from the
pinned NYLL NormSubgroup.lean, prefix their namespace with Langlands.NYLL,
and replace each theorem with a Prop-valued Statement definition. Preserve
the universe, the full telescopes, binder kinds and order and every
hypothesis; underscore the containment argument names that the conclusions
do not mention. Omit the proofs and the simp attribute. See the paired
Markdown and licenses/NYLL/LICENSE and NOTICE.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

universe u

section maximalUnramifiedFields

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- Target identifying the maximal unramified field with absolute inertia. -/
def maximalUnramifiedField_eq_fieldInertiaStatement
    (D : DegreeData G) (L : ClosedSubgroup G) : Prop :=
  D.maximalUnramifiedField L = D.fieldInertia L

/-- Target: membership in the maximal unramified field is the expected
inertia condition. -/
def mem_maximalUnramifiedField_iffStatement
    (D : DegreeData G) (L : ClosedSubgroup G) (g : G) : Prop :=
  g ∈ D.maximalUnramifiedField L ↔ g ∈ L ∧ D.degree g = 1

/-- Target: the maximal unramified field of `L` lies over `L`, that is, its
subgroup lies below `G_L`. -/
def maximalUnramifiedField_leStatement (D : DegreeData G) (L : ClosedSubgroup G) :
    Prop :=
  (D.maximalUnramifiedField L).toSubgroup ≤ L.toSubgroup

/-- Target: if `G_L ≤ G_K`, the subgroup of the maximal unramified field of
`L` lies below `G_K`. -/
def maximalUnramifiedField_le_of_leStatement (D : DegreeData G)
    {L K : ClosedSubgroup G} (_hLK : L.toSubgroup ≤ K.toSubgroup) : Prop :=
  (D.maximalUnramifiedField L).toSubgroup ≤ K.toSubgroup

/-- Target: monotonicity of maximal unramified fields. -/
def maximalUnramifiedField_monoStatement (D : DegreeData G)
    {K L : ClosedSubgroup G} (_hLK : L.toSubgroup ≤ K.toSubgroup) : Prop :=
  (D.maximalUnramifiedField L).toSubgroup ≤
    (D.maximalUnramifiedField K).toSubgroup

end DegreeData

end maximalUnramifiedFields

end
end Langlands.NYLL.ClassFormation
