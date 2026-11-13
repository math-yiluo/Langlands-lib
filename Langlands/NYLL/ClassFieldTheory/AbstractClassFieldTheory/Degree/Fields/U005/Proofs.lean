/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.Statements

/-!
# NYLL M010.005: every abstract field lies over the base field

Modified by Worker 187: extract the source theorem into this focused module,
prefix its namespace with Langlands.NYLL, and state its type using the
published le_baseFieldStatement. Retain the original le_top proof.
See the paired Markdown and licenses/NYLL/LICENSE and NOTICE.
-/

namespace Langlands.NYLL.ClassFormation

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- Every abstract field lies over the distinguished base field. -/
theorem le_baseField (K : ClosedSubgroup G) : le_baseFieldStatement K :=
  le_top

end Langlands.NYLL.ClassFormation
