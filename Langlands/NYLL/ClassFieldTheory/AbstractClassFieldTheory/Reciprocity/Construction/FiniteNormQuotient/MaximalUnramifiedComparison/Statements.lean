/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FiniteNormQuotient.MaximalUnramifiedComparison.Definitions

/-!
# Target: the comparison map on maximal-unramified norm classes

Modified by Worker 5264, 15 November 2026: extract the statement of M039.022
from
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FiniteNormQuotient.lean`
at fbd320cd8b1b06487c58227e92eb135794267709, prefix the namespace with
`Langlands.NYLL`, replace the source imports by the module of the comparison
map (M039.021), which imports the published class maps, and replace
`extensionSubgroup K L hLK` in the finiteness binder by its exact
`Subgroup.subgroupOf` body, as the published finite norm quotient does.
Replace the source theorem by a Prop-valued definition with the `Statement`
suffix, omitting its proof and its `@[simp]` attribute, and reword the
declaration docstring to describe the proposition. The open, the variable
declaration and the other binders are unchanged. Omit the rest of the source
file. See the paired Markdown and `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

open KummerTheory

noncomputable section

section quotientMaps

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- The proposition, from the source theorem
`maximalUnramifiedToFiniteNormQuotient_maximalUnramifiedNormClass`, that the
comparison to a finite norm quotient carries the maximal-unramified class of
`a` to its finite-level class. -/
def maximalUnramifiedToFiniteNormQuotient_maximalUnramifiedNormClassStatement
    (D : DegreeData G) (A : Rep ℤ G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hfinite : Finite (K.toSubgroup ⧸ (L.toSubgroup.subgroupOf K.toSubgroup))]
    (a : ambientFixedAddSubgroup A K) : Prop :=
    D.maximalUnramifiedToFiniteNormQuotient A K L hLK
        (D.maximalUnramifiedNormClass A K L a) =
      finiteNormClass A K L hLK a

end DegreeData

end quotientMaps

end
end Langlands.NYLL.ClassFormation
