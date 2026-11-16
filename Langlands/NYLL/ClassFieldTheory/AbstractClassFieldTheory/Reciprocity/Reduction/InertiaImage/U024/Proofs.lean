/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Reduction.InertiaImage.Statements

/-!
# NYLL M077.024: normality of the inertia image

Modified by Worker 756, 16 November 2026: extract the proof of M077.024
`FiniteGaloisSubextension.inertiaImage_normal` (lines 471–479) of
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Reduction.lean`
at `fbd320cd8b1b06487c58227e92eb135794267709`, prefix the namespace with
`Langlands.NYLL`, replace the source imports by the published statement
module, omit the unused `open KummerTheory`, and state the theorem as the
published Statement applied to the source parameters. The proof term is the
source's. The paired Markdown records every modification. See
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
/-- The inertia image is normal, since it is the image of the normal
inertia subgroup under a surjective quotient map. -/
theorem inertiaImage_normal (D : DegreeData G)
    (L : FiniteGaloisSubextension K) : inertiaImage_normalStatement D L := by
  exact (inferInstance : (D.fieldInertiaWithin K).Normal).map
    (QuotientGroup.mk' (extensionSubgroup K L.field L.below))
    (QuotientGroup.mk'_surjective
      (extensionSubgroup K L.field L.below))

end FiniteGaloisSubextension

end GroupOnly

end

end Langlands.NYLL.ClassFormation
