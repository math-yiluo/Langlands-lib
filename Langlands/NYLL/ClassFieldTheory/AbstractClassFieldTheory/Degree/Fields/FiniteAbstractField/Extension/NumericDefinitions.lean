/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteAbstractField.Extension.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteExtension.NumericDefinitions

/-!
# NYLL M010: positive relative residue degree of a finite field extension

Modified by Worker 171: extract M010.136 from the pinned NYLL
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Fields.lean`, prefix
the namespace with `Langlands.NYLL`, and replace the source module imports by
focused published imports. Universe, binders, docstring and body are otherwise
unchanged. See the paired Markdown and `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace FiniteAbstractFieldExtension

/-- The positive relative residue degree. -/
noncomputable def residueDegree (E : FiniteAbstractFieldExtension G)
    (D : DegreeData G) : ℕ+ :=
  E.toFiniteAbstractExtension.residueDegree D

end FiniteAbstractFieldExtension

end
end Langlands.NYLL.ClassFormation
