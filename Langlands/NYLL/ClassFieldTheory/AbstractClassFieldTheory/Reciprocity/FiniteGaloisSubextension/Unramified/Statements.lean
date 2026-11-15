/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteGaloisSubextension.Definitions

/-!
# Target: the inertia criterion for unramified finite Galois extensions

Modified by Worker 5264, 15 November 2026: state the source theorem M040.021
`FiniteGaloisSubextension.isUnramified_iff_inertia_le` of
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/FiniteGaloisSubextension.lean`
at fbd320cd8b1b06487c58227e92eb135794267709 as a Prop-valued Statement
definition. Prefix the namespace with `Langlands.NYLL`, append `Statement`
to the name, replace the source import by the published
`FiniteGaloisSubextension.Definitions` module, keep the source universe,
section, variables, binders and statement unchanged, and omit the proof, the
opens of `KummerTheory` and `CyclicCohomology` (none of their names occur in
this statement) and the rest of the source file. See the paired Markdown and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

universe u

section GroupOnly

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace FiniteGaloisSubextension

variable {K : ClosedSubgroup G}

/-- Target: unramifiedness is the canonical inertia-containment condition. -/
def isUnramified_iff_inertia_leStatement (L : FiniteGaloisSubextension K)
    (D : DegreeData G) : Prop :=
    L.IsUnramified D ↔
      K.toSubgroup ⊓ D.degree.toMonoidHom.ker ≤ L.field.toSubgroup

end FiniteGaloisSubextension

end GroupOnly

end
end Langlands.NYLL.ClassFormation
