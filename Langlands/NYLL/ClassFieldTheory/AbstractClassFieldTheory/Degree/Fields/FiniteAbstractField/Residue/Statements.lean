/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteAbstractField.Residue.Definitions

/-!
# NYLL M010: residue-degree target for the distinguished base field

Modified by Worker 171: state the source theorem M010.128
`FiniteAbstractField.base_residueDegree` of the pinned NYLL
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Fields.lean` as the
Prop-valued definition `base_residueDegreeStatement`, prefix the namespace
with `Langlands.NYLL`, and use a focused published import. The source
statement, universe and instance binders are unchanged; the source proof and
`@[simp]` attribute belong to the later proof. See the paired Markdown and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace FiniteAbstractField

/-- Positive-natural specialization of the base-field residue degree. -/
def base_residueDegreeStatement (D : DegreeData G) : Prop :=
  (FiniteAbstractField.base G).residueDegree D = 1

end FiniteAbstractField

end
end Langlands.NYLL.ClassFormation
