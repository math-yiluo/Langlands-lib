/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.Statements

/-!
# NYLL M010.011: the field image as a subgroup map

Modified by Worker 188: extract M010.011 from the pinned NYLL Fields source,
prefix the namespace with Langlands.NYLL, and state the conclusion using the
published fieldImage_eq_mapStatement. Retain the source witness proof after
unfolding that target. See the paired Markdown and licenses/NYLL/LICENSE and
NOTICE.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- The field's degree image is the image of its subgroup under the ambient degree map. -/
theorem fieldImage_eq_map (D : DegreeData G) (K : ClosedSubgroup G) :
    fieldImage_eq_mapStatement D K := by
  change D.fieldImage K = K.toSubgroup.map D.degree.toMonoidHom
  ext z
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k.1, k.2, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g, hg⟩, rfl⟩

end DegreeData

end
end Langlands.NYLL.ClassFormation
