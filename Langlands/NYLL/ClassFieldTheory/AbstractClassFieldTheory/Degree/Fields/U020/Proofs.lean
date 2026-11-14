/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.U004.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.U011.Proofs

/-!
# The residue cardinal of the NYLL distinguished base field

Modified by Worker 238: extract M010.020, prefix the namespace with
Langlands.NYLL, and use the published Statement as the theorem's result.
Replace the broad source imports with the two published support proofs.
Retain the source proof body and omit the source simp attribute.
See the paired Markdown and licenses/NYLL/LICENSE and NOTICE.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- The distinguished base field has absolute residue degree one, without
passing through a natural-valued subgroup index. -/
theorem residueDegreeCardinal_baseField (D : DegreeData G) :
    residueDegreeCardinal_baseFieldStatement D := by
  change
    intersectionIndexCardinal (D.fieldImage (baseField G))
      (⊤ : Subgroup ZHatMul) = 1
  rw [D.fieldImage_eq_map, baseField_toSubgroup,
    Subgroup.map_top_of_surjective _ D.degree_surjective]
  change Cardinal.mk (↥(⊤ : Subgroup ZHatMul) ⧸ ⊤) = 1
  let : Subsingleton (↥(⊤ : Subgroup ZHatMul) ⧸
      (⊤ : Subgroup ↥(⊤ : Subgroup ZHatMul))) :=
    QuotientGroup.subsingleton_quotient_top
  exact Cardinal.mk_eq_one _

end DegreeData

end
end Langlands.NYLL.ClassFormation
