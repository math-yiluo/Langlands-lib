/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.Supplement.TotalRamificationStatements
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.AbstractExtension.U047.Proofs

/-!
# NYLL M010.064: total ramification of a Galois subextension as image containment

Modified by Worker 79: extract M010.064 from the pinned NYLL Fields
source, prefix the namespace with Langlands.NYLL, use focused published
imports, and state the result using the exact named target. The source
proof term is retained. See the paired Markdown and licenses/NYLL/LICENSE
and NOTICE for the complete modification and attribution record.
-/

namespace Langlands.NYLL.ClassFormation

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

namespace GaloisSubextension

variable {K : ClosedSubgroup G}

/-- Total ramification is the canonical equality of degree images. -/
theorem isTotallyRamified_iff_image_le (L : GaloisSubextension K)
    (D : DegreeData G) :
    isTotallyRamified_iff_image_leStatement L D :=
  L.toAbstractExtension.isTotallyRamified_iff_image_le D

end GaloisSubextension

end DegreeData

end Langlands.NYLL.ClassFormation
