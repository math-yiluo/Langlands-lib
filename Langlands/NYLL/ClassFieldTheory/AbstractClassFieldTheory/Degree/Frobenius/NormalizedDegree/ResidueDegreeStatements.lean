/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteResidueExtension.ResidueDegreeDefinitions

/-!
# NYLL M011: relative and absolute residue degrees

Modified by Worker 357: extract M011.017, prefix its namespace with
Langlands.NYLL, use the focused published residue-degree import, and turn
the source theorem into a Prop-valued target without its proof.
See the paired Markdown and licenses/NYLL/LICENSE and NOTICE.
-/

namespace Langlands.NYLL.ClassFormation

variable {G : Type*} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- The relative residue degree times the base's absolute residue degree
is the field's absolute residue degree. -/
def FiniteResidueAbstractExtension.residueDegree_mul_absoluteResidueDegreeStatement
    (D : DegreeData G) (E : FiniteResidueAbstractExtension D) : Prop :=
  (E.residueDegree : ℕ) * (E.base.residueDegree : ℕ) =
    (E.field.residueDegree : ℕ)

end DegreeData
end Langlands.NYLL.ClassFormation
