/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.InfiniteUnitNormSubgroup.Definitions

/-!
# The universal unit norm group

Modified by Worker 5264, 15 November 2026: extract the definition M050.003
`ValuationData.infiniteUnitNormSubgroup` of
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/InfiniteUnitNormSubgroup.lean`
at fbd320cd8b1b06487c58227e92eb135794267709. Prefix the namespace with
`Langlands.NYLL`, replace the source import by the focused published import,
and omit the rest of the source file, the unused `universe u` and the unused
`open CyclicCohomology`, `open CategoryTheory` and `open scoped BigOperators`.
The binders, docstring and body are unchanged. See the paired Markdown and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

open KummerTheory

noncomputable section

variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace ValuationData

variable {D : DegreeData G} {A : Rep ℤ G}

/-- The universal unit norm group
`N_{E/K} U_E = ⋂_M N_{M/K} U_M`. -/
def infiniteUnitNormSubgroup
    (v : ValuationData D A) (E : ClosedSubgroup G)
    (K : FiniteAbstractField G) :
    AddSubgroup (ambientFixedAddSubgroup A K.field) :=
  ⨅ M : FiniteIntermediateField E K.field,
    v.finiteIntermediateUnitNormRange E K M

end ValuationData

end

end Langlands.NYLL.ClassFormation
