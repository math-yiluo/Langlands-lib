/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.Definitions

/-!
# The additive degree image

Modified by Worker 199: extract M011.001 from the pinned NYLL Frobenius
source, prefix the namespace with Langlands.NYLL, and replace the source's
Fields import with its published focused definitions. Preserve the original
parameters, construction, docstring and noncomputable section.
See the paired Markdown and licenses/NYLL/LICENSE and NOTICE.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- The image `d(G_K)`, written additively inside `ℤ̂`. -/
def fieldImageAdd (D : DegreeData G) (K : ClosedSubgroup G) : AddSubgroup ZHat :=
  Subgroup.toAddSubgroup' (D.fieldImage K)

end DegreeData

end
end Langlands.NYLL.ClassFormation
