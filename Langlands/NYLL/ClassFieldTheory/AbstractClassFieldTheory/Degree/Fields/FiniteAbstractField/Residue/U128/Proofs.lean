/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteAbstractField.Residue.Statements

/-!
# NYLL M010.128: the base finite abstract field has residue degree one

Modified by Worker 473: prove the published target
`base_residueDegreeStatement` (M010.128) of the pinned NYLL
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Fields.lean`, with
the namespace prefixed by `Langlands.NYLL` and a focused published import.
The source proof passes through the cardinal lemma M010.020
`residueDegreeCardinal_baseField`, whose proof is not published; this proof
instead inlines that lemma's argument (the degree image of the base field is
everything, by `D.degree_surjective`, so the actual residue quotient is a
subsingleton) at the level of `Nat.card`. The universe, binders and source
`@[simp]` attribute are retained. See the paired Markdown and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace FiniteAbstractField

/-- Positive-natural specialization of the base-field residue degree. -/
@[simp] theorem base_residueDegree (D : DegreeData G) :
    base_residueDegreeStatement D := by
  apply Subtype.ext
  change Nat.card (D.residueQuotient (baseField G)) = 1
  have himage : D.fieldImage (baseField G) = ⊤ := by
    rw [D.fieldImage_eq_map, baseField_toSubgroup]
    exact Subgroup.map_top_of_surjective _ D.degree_surjective
  have hsub : Subsingleton (D.residueQuotient (baseField G)) := by
    change Subsingleton (↥(⊤ : Subgroup ZHatMul) ⧸
      (D.fieldImage (baseField G)).subgroupOf ⊤)
    rw [himage, Subgroup.subgroupOf_self]
    exact QuotientGroup.subsingleton_quotient_top
  have hne : Nonempty (D.residueQuotient (baseField G)) := ⟨QuotientGroup.mk 1⟩
  exact Nat.card_unique

end FiniteAbstractField

end
end Langlands.NYLL.ClassFormation
