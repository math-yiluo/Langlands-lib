/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.Supplement.TotalRamificationStatements
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.AbstractExtension.U047.Proofs

/-!
# NYLL M010.076: total ramification of a finite extension as image containment

Modified by Worker 79: extract M010.076 from the pinned NYLL Fields
source, prefix the namespace with Langlands.NYLL, use focused published
imports, and state the result using the exact named target. The source
proof term is retained. See the paired Markdown and licenses/NYLL/LICENSE
and NOTICE for the complete modification and attribution record.
-/

namespace Langlands.NYLL.ClassFormation

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

namespace FiniteAbstractExtension

variable (E : FiniteAbstractExtension G)

/-- Finite totally ramified extensions satisfy the same degree-image
characterization as their underlying abstract extensions. -/
theorem isTotallyRamified_iff_image_le (D : DegreeData G) :
    isTotallyRamified_iff_image_leStatement E D :=
  E.toAbstractExtension.isTotallyRamified_iff_image_le D

end FiniteAbstractExtension

end DegreeData

end Langlands.NYLL.ClassFormation
