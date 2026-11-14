/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Frobenius.FieldImageIndex.Statements
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteResidue.U026.Proofs
import Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.U013.Proofs

/-!
# NYLL M011.003: the additive degree image is the residue-degree multiple range

Modified by Worker 356, using Worker 5264's supplied proof adaptation:
extract M011.003 from the pinned NYLL Frobenius source, prefix its namespace
with Langlands.NYLL, use focused published imports, and conclude the exact
published target. A private lemma repeats the source M011.002 index argument
so this focused candidate does not import its pending sibling proof. The
main proof applies the published M009.013 classification as in the source.
See the paired Markdown and licenses/NYLL/LICENSE and NOTICE.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- Local form of the source M011.002 index calculation. -/
private theorem u003_fieldImageAdd_index (D : DegreeData G)
    (K : FiniteResidueAbstractField D) :
    fieldImageAdd_indexStatement D K := by
  change (D.fieldImage K.field).index = (K.residueDegree : ℕ)
  rw [← Subgroup.relIndex_top_right]
  change Nat.card (D.residueQuotient K.field) = (K.residueDegree : ℕ)
  exact (FiniteResidueAbstractField.residueDegree_coe K).symm

/-- Finite residue degree identifies the additive image with its multiple range. -/
theorem fieldImageAdd_eq_mulNat_range (D : DegreeData G)
    (K : FiniteResidueAbstractField D) :
    fieldImageAdd_eq_mulNat_rangeStatement D K :=
  zHatAddSubgroup_eq_mulNat_range_of_index_eq (D.fieldImageAdd K.field)
    K.residueDegree.property (u003_fieldImageAdd_index D K)

end DegreeData

end
end Langlands.NYLL.ClassFormation
