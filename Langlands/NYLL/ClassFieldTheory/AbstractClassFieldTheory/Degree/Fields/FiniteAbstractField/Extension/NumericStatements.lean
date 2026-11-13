/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteAbstractField.Extension.NumericDefinitions

/-!
# NYLL M010: residue degree equals degree for unramified finite field extensions

Modified by Worker 171: state the source theorem M010.138
`FiniteAbstractFieldExtension.residueDegree_eq_degree_of_isUnramified` of the
pinned NYLL `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Fields.lean`
as the Prop-valued definition `residueDegree_eq_degree_of_isUnramifiedStatement`,
prefix the namespace with `Langlands.NYLL`, and use a focused published import.
The source binders and conclusion are unchanged; the source proof belongs to
the later proof. See the paired Markdown and `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace FiniteAbstractFieldExtension

-- The source hypothesis name `hE` is kept although the proposition never mentions it.
set_option linter.unusedVariables false in
/-- In an unramified finite field extension, the positive relative residue
degree is the positive extension degree. -/
def residueDegree_eq_degree_of_isUnramifiedStatement
    (E : FiniteAbstractFieldExtension G) (D : DegreeData G)
    (hE : E.IsUnramified D) : Prop :=
  (E.residueDegree D : ℕ) = (E.degree : ℕ)

end FiniteAbstractFieldExtension

end
end Langlands.NYLL.ClassFormation
