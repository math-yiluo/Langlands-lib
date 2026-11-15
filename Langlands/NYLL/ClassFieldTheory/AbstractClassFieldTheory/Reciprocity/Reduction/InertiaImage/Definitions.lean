/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteGaloisSubextension.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.Definitions

/-!
# The inertia image in a finite Galois quotient

Modified by Worker 5264, 15 November 2026: extract the definition M077.023
`FiniteGaloisSubextension.inertiaImage` of
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Reduction.lean`
at fbd320cd8b1b06487c58227e92eb135794267709. Prefix the namespace with
`Langlands.NYLL`, replace the source imports by focused published imports,
and omit the rest of the source file and the unused `open KummerTheory`.
The section `GroupOnly`, its variables, the binders, the docstring and the
body are unchanged. See the paired Markdown and `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

open CyclicCohomology

noncomputable section

universe u

section GroupOnly

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

namespace FiniteGaloisSubextension

variable {K : ClosedSubgroup G}

/-- The inertia subgroup of `G(L/K)`: the image of `I_K` in the actual
finite quotient.  Its fixed field is `L ∩ K̃` in the notation of. -/
def inertiaImage (D : DegreeData G) (L : FiniteGaloisSubextension K) :
    Subgroup L.extensionQuotient :=
  (D.fieldInertiaWithin K).map
    (QuotientGroup.mk' (extensionSubgroup K L.field L.below))

end FiniteGaloisSubextension

end GroupOnly

end

end Langlands.NYLL.ClassFormation
