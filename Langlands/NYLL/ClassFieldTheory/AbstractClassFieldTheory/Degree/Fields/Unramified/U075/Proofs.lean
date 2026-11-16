/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.Unramified.Statements

/-!
# NYLL M010.075: the inertia criterion for unramified finite extensions

Modified by Worker 5264, 15 November 2026: prove the published target
`DegreeData.FiniteAbstractExtension.isUnramified_iff_inertia_leStatement`
(M010.075) for the source theorem
`DegreeData.FiniteAbstractExtension.isUnramified_iff_inertia_le` in
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Fields.lean` at
fbd320cd8b1b06487c58227e92eb135794267709. Prefix the namespace with
`Langlands.NYLL`, give the theorem the published proposition as its type,
begin the proof with `show` stating it unfolded, and replace the source
term `E.toAbstractExtension.isUnramified_iff_inertia_le D`, whose proof
M010.046 is not in the Library, by `Iff.rfl`, the source proof of M010.046
itself. Replace the source imports by the published statement module and
omit the open of `CyclicCohomology` and the rest of the source file. See the
paired Markdown and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

namespace FiniteAbstractExtension

variable (E : FiniteAbstractExtension G)

/-- Finite unramified extensions satisfy the same inertia-containment
characterization as their underlying abstract extensions. -/
theorem isUnramified_iff_inertia_le (D : DegreeData G) :
    isUnramified_iff_inertia_leStatement E D := by
  show E.IsUnramified D ↔
    E.base.toSubgroup ⊓ D.degree.toMonoidHom.ker ≤ E.field.toSubgroup
  exact Iff.rfl

end FiniteAbstractExtension

end DegreeData

end

end Langlands.NYLL.ClassFormation
