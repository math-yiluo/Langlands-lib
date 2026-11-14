/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Frobenius.FieldImageIndex.Statements
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteResidue.U026.Proofs

/-!
# NYLL M011.002: the index of the additive degree image

Modified by Worker 356, with the proof adaptation supplied by Worker 5264:
extract M011.002 from the pinned NYLL Frobenius source, prefix the namespace
with Langlands.NYLL, import the focused published target and residue-degree
proof, and state the theorem through the exact target proposition. Retain
the source proof route, qualifying residueDegree_coe explicitly. Omit the
source simp attribute because the theorem concludes the target proposition.
See the paired Markdown and licenses/NYLL/LICENSE and NOTICE.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- The additive degree image has index equal to the positive residue degree. -/
theorem fieldImageAdd_index (D : DegreeData G)
    (K : FiniteResidueAbstractField D) :
    fieldImageAdd_indexStatement D K := by
  change (D.fieldImage K.field).index = (K.residueDegree : ℕ)
  rw [← Subgroup.relIndex_top_right]
  change Nat.card (D.residueQuotient K.field) = (K.residueDegree : ℕ)
  exact (FiniteResidueAbstractField.residueDegree_coe K).symm

end DegreeData

end
end Langlands.NYLL.ClassFormation
