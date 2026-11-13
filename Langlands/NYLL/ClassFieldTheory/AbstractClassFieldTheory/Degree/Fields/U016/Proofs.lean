/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.Statements

/-!
# Internal field inertia membership

Modified by Worker 288: extract source unit M010.016 from
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Fields.lean` at commit
`fbd320cd8b1b06487c58227e92eb135794267709`. Prefix the namespace with
`Langlands.NYLL`, state the theorem through the published Statement definition,
and retain the source proof and simp attribute. See the paired Markdown and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation.DegreeData

noncomputable section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- Membership in internal field inertia is equivalent to having ambient degree one. -/
@[simp]
theorem mem_fieldInertiaWithin_iff (D : DegreeData G) (K : ClosedSubgroup G)
    (k : K.toSubgroup) : mem_fieldInertiaWithin_iffStatement D K k :=
  Iff.rfl

end
end Langlands.NYLL.ClassFormation.DegreeData
