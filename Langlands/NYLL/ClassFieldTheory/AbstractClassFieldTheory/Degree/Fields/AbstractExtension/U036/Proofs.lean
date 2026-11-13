/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.AbstractExtension.CardinalStatements
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.U011.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Indices.U014.Proofs

/-!
# Cardinal residue-degree compatibility for an abstract extension

Modified by Worker 183: extract NYLL M010.036, prefix its namespace with
Langlands.NYLL, use the published Statement as its type, and explicitly
unfold the published product Statement when applying its proof.
The source subgroup-image tower proof is preserved.
See the paired Markdown and licenses/NYLL/LICENSE and NOTICE.
-/

namespace Langlands.NYLL.ClassFormation

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData.AbstractExtension

/-- The relative residue cardinal times the base residue cardinal is the field residue cardinal. -/
theorem relativeResidueDegreeCardinal_mul_residueDegreeCardinal
    (E : AbstractExtension G) (D : DegreeData G) :
    relativeResidueDegreeCardinal_mul_residueDegreeCardinalStatement E D := by
  change
    intersectionIndexCardinal
        (E.field.toSubgroup.map D.degree.toMonoidHom)
        (E.base.toSubgroup.map D.degree.toMonoidHom) *
      intersectionIndexCardinal (D.fieldImage E.base) (⊤ : Subgroup ZHatMul) =
        intersectionIndexCardinal (D.fieldImage E.field) (⊤ : Subgroup ZHatMul)
  rw [D.fieldImage_eq_map, D.fieldImage_eq_map]
  simpa only [relativeIndexCardinal_mulStatement, relativeIndexCardinal] using
    (relativeIndexCardinal_mul
      (Subgroup.map_mono (f := D.degree.toMonoidHom) E.below)
      (show E.base.toSubgroup.map D.degree.toMonoidHom ≤
        (⊤ : Subgroup ZHatMul) from le_top))

end DegreeData.AbstractExtension
end Langlands.NYLL.ClassFormation
