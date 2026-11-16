/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.Unramified.Statements

/-!
# NYLL M010.046: the inertia criterion for unramified abstract extensions

Modified by Worker 5264, 15 November 2026: prove the published target
`DegreeData.AbstractExtension.isUnramified_iff_inertia_leStatement`
(M010.046) by the source proof of
`DegreeData.AbstractExtension.isUnramified_iff_inertia_le` in
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Fields.lean` at
fbd320cd8b1b06487c58227e92eb135794267709. Prefix the namespace with
`Langlands.NYLL`, give the theorem the published proposition as its type,
begin the proof with `show` stating it unfolded, replace the source imports
by the published statement module and omit the open of `CyclicCohomology`
and the rest of the source file. See the paired Markdown and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

namespace AbstractExtension

/-- An extension is unramified exactly when the inertia subgroup of its base
is contained in the subgroup representing its field.  The containment needed
to form the extension is carried by `E`. -/
theorem isUnramified_iff_inertia_le (E : AbstractExtension G) (D : DegreeData G) :
    isUnramified_iff_inertia_leStatement E D := by
  show E.IsUnramified D ↔
    E.base.toSubgroup ⊓ D.degree.toMonoidHom.ker ≤ E.field.toSubgroup
  exact Iff.rfl

end AbstractExtension

end DegreeData

end

end Langlands.NYLL.ClassFormation
