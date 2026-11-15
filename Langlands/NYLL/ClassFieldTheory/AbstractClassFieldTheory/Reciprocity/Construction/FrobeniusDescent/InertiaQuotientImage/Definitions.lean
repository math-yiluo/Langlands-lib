/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusLift.Definitions
import Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions

/-!
# The image of `G_L` in the inertia quotient `G_K / I_L`

Modified by Worker 5264, 15 November 2026: port the source definition
M017.001 `extensionImageInInertiaQuotient` of
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusDescent.lean`
at fbd320cd8b1b06487c58227e92eb135794267709. Prefix the namespace with
`Langlands.NYLL`, replace the source imports by focused published imports,
keep the source variable declaration, docstring, binders and body, and omit
the rest of the source file. See the paired Markdown and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

open CyclicCohomology

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- The image of `G_L` in `G_K / I_L`. -/
def extensionImageInInertiaQuotient (D : DegreeData G)
    (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L hLK).Normal] :
    Subgroup (K.toSubgroup ⧸ D.extensionInertiaWithin K L hLK) :=
  (extensionSubgroup K L hLK).map
    (QuotientGroup.mk' (D.extensionInertiaWithin K L hLK))

end DegreeData

end

end Langlands.NYLL.ClassFormation
