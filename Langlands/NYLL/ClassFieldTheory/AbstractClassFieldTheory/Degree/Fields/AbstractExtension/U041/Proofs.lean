/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.AbstractExtension.StructuralStatements
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Indices.U014.Proofs

/-!
# NYLL M010.041: cardinal degrees multiply in an arbitrary tower

Modified by Worker 188: extract M010.041 from the pinned NYLL Fields
source, prefix the namespace with Langlands.NYLL, use focused published
imports, and state the result using the exact named target. The source
proof route is retained. See the paired Markdown and licenses/NYLL/LICENSE
and NOTICE for the complete modification and attribution record.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

namespace AbstractExtension.Tower

/-- Cardinal degrees multiply in an arbitrary abstract-extension tower. -/
theorem degreeCardinal_mul (T : AbstractExtension.Tower G) :
    degreeCardinal_mulStatement T := by
  exact relativeIndexCardinal_mul T.top_le_middle T.middle_le_base

end AbstractExtension.Tower

end DegreeData

end
end Langlands.NYLL.ClassFormation
