/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.AbstractExtension.CardinalStatements
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Indices.U025.Proofs

/-!
# Cardinal fundamental identity for an abstract extension

Modified by Worker 183: extract NYLL M010.035, prefix its namespace with
Langlands.NYLL and use its published Statement as the theorem type.
Integrator reuses the published M006.025 image/kernel factorization.
See the paired Markdown and licenses/NYLL/LICENSE and NOTICE.
-/

namespace Langlands.NYLL.ClassFormation

universe u v

variable {G : Type u} [Group G]

namespace DegreeData.AbstractExtension

variable [TopologicalSpace G]

/-- The cardinal degree is the relative residue cardinal times the ramification cardinal. -/
theorem degreeCardinal_eq_relativeResidueDegreeCardinal_mul_relativeRamificationIndexCardinal
    (E : AbstractExtension G) (D : DegreeData G) :
    degreeCardinal_eq_relativeResidueDegreeCardinal_mul_relativeRamificationIndexCardinalStatement
      E D := by
  unfold degreeCardinal_eq_relativeResidueDegreeCardinal_mul_relativeRamificationIndexCardinalStatement
  simpa [relativeIndexCardinal_eq_map_mul_inf_kerStatement,
    degreeCardinal, relativeResidueDegreeCardinal,
    relativeRamificationIndexCardinal] using
    (relativeIndexCardinal_eq_map_mul_inf_ker D.degree.toMonoidHom E.below)

end DegreeData.AbstractExtension
end Langlands.NYLL.ClassFormation
