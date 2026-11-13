/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.Statements

/-!
# NYLL M010.013: membership in field inertia

Modified by Worker 287: isolate M010.013, prefix the namespace with
Langlands.NYLL, import the published target and state the theorem through it.
Retain the source proof `Iff.rfl`; omit the source simp attribute.
See the paired Markdown and licenses/NYLL/LICENSE and NOTICE.
-/

namespace Langlands.NYLL.ClassFormation.DegreeData

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- Field inertia consists of field elements whose ambient degree is one. -/
theorem mem_fieldInertia_iff (D : DegreeData G) (K : ClosedSubgroup G) (g : G) :
    mem_fieldInertia_iffStatement D K g :=
  Iff.rfl

end Langlands.NYLL.ClassFormation.DegreeData
