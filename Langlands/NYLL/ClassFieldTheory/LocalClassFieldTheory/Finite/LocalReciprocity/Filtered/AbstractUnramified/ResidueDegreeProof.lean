/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.Filtered.AbstractUnramified.ResidueDegreeStatement

/-!
# NYLL M330.005: absolute and relative residue degrees

Modified by Worker 317, using Worker 305's checked quotient-identification
route: extract M330.005, prefix the namespace with `Langlands.NYLL`, import
the published statement, and replace the source cardinal-multiplication
proof by direct identification of the actual residue quotient types.
The source theorem name and full telescope are retained. See the paired
Markdown and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open ClassFormation

universe u

/-- For a field finite over the distinguished abstract base, the absolute
residue degree agrees with its relative residue degree over that base. -/
theorem finiteAbstractField_residueDegree_eq_relativeResidueDegree
    {G : Type u} [Group G] [TopologicalSpace G]
    (D : DegreeData G) (H : FiniteAbstractField G) :
    finiteAbstractField_residueDegree_eq_relativeResidueDegreeStatement D H := by
  change Nat.card (D.residueQuotient H.field) =
    Nat.card
      (↥((baseField G).toSubgroup.map D.degree.toMonoidHom) ⧸
        (H.field.toSubgroup.map D.degree.toMonoidHom).subgroupOf
          ((baseField G).toSubgroup.map D.degree.toMonoidHom))
  unfold DegreeData.residueQuotient
  rw [D.fieldImage_eq_map, baseField_toSubgroup,
    Subgroup.map_top_of_surjective _ D.degree_surjective]

end Langlands.NYLL.LocalClassFieldTheory
