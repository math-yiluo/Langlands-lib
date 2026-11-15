/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Reduction.InertiaImage.Definitions

/-!
# Target: normality of the inertia image

Modified by Worker 5264, 15 November 2026: state the source theorem M077.024
`FiniteGaloisSubextension.inertiaImage_normal` of
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Reduction.lean`
at fbd320cd8b1b06487c58227e92eb135794267709 as a Prop-valued Statement
definition. Prefix the namespace with `Langlands.NYLL`, append
`Statement` to the name, omit the proof and the unused
`open KummerTheory`, and keep the source section variables and its
`omit [IsTopologicalGroup G] in`. See the paired Markdown and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

open CyclicCohomology

noncomputable section

universe u

section GroupOnly

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

namespace FiniteGaloisSubextension

variable {K : ClosedSubgroup G}

omit [IsTopologicalGroup G] in
/-- Target: the inertia image is normal, since it is the image of the normal
inertia subgroup under a surjective quotient map. -/
def inertiaImage_normalStatement (D : DegreeData G)
    (L : FiniteGaloisSubextension K) : Prop :=
    (L.inertiaImage D).Normal

end FiniteGaloisSubextension

end GroupOnly

end

end Langlands.NYLL.ClassFormation
