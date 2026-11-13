/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.AbstractExtension.StructuralStatements

/-!
# NYLL M010.047: total ramification as containment of degree images

Modified by Worker 188: extract M010.047 from the pinned NYLL Fields
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

namespace AbstractExtension

/-- Total ramification is the containment of the base degree image in the field image. -/
theorem isTotallyRamified_iff_image_le (E : AbstractExtension G) (D : DegreeData G) :
    isTotallyRamified_iff_image_leStatement E D :=
  Iff.rfl

end AbstractExtension

end DegreeData

end
end Langlands.NYLL.ClassFormation
