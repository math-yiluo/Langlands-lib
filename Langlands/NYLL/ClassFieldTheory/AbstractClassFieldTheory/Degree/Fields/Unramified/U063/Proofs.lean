/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.Unramified.Statements

/-!
# NYLL M010.063: the inertia criterion for unramified Galois subextensions

Modified by Worker 5264, 15 November 2026: prove the published target
`DegreeData.GaloisSubextension.isUnramified_iff_inertia_leStatement`
(M010.063) for the source theorem
`DegreeData.GaloisSubextension.isUnramified_iff_inertia_le` in
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Fields.lean` at
fbd320cd8b1b06487c58227e92eb135794267709. Prefix the namespace with
`Langlands.NYLL`, give the theorem the published proposition as its type,
begin the proof with `show` stating it unfolded, and replace the source
term `L.toAbstractExtension.isUnramified_iff_inertia_le D`, whose proof
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

namespace GaloisSubextension

variable {K : ClosedSubgroup G}

/-- Unramifiedness is the canonical inertia-containment condition. -/
theorem isUnramified_iff_inertia_le (L : GaloisSubextension K)
    (D : DegreeData G) :
    isUnramified_iff_inertia_leStatement L D := by
  show L.IsUnramified D ↔
    K.toSubgroup ⊓ D.degree.toMonoidHom.ker ≤ L.field.toSubgroup
  exact Iff.rfl

end GaloisSubextension

end DegreeData

end

end Langlands.NYLL.ClassFormation
