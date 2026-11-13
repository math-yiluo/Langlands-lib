/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.Statements

/-!
# The underlying subgroup of the NYLL base field

Modified by Worker 186: extract source unit M010.004, prefix the namespace
with Langlands.NYLL, and state the theorem using the published Statement.
Retain the original reflexivity proof and omit the source simp attribute.
See the paired Markdown and licenses/NYLL/LICENSE and NOTICE.
-/

namespace Langlands.NYLL.ClassFormation

universe u

/-- The distinguished base field is represented by the full ambient subgroup. -/
theorem baseField_toSubgroup (G : Type u) [Group G] [TopologicalSpace G] :
    baseField_toSubgroupStatement G :=
  rfl

end Langlands.NYLL.ClassFormation
