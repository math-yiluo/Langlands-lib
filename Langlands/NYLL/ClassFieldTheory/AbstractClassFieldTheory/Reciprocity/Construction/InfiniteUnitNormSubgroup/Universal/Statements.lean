/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.InfiniteUnitNormSubgroup.Universal.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.NormSubgroup.InfiniteNorm.Definitions

/-!
# Targets: membership in the universal unit norm group

Modified by Worker 5264, 15 November 2026: state the source theorems M050.004
`ValuationData.mem_infiniteUnitNormSubgroup_iff` and M050.006
`ValuationData.infiniteUnitNormSubgroup_le_normSubgroup` of
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/InfiniteUnitNormSubgroup.lean`
at fbd320cd8b1b06487c58227e92eb135794267709 as Prop-valued Statement
definitions. Prefix the namespace with `Langlands.NYLL`, append `Statement`
to each name, replace the source import by focused published imports, omit
the proofs, the `@[simp]` attribute of M050.004 (a definition of a
proposition is not a simp lemma), the rest of the source file, the unused
`universe u` and the unused `open CyclicCohomology`, `open CategoryTheory` and
`open scoped BigOperators`. See the paired Markdown and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

open KummerTheory

noncomputable section

variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace ValuationData

variable {D : DegreeData G} {A : Rep ℤ G}

/-- Target: characterizes `a ∈ v.infiniteUnitNormSubgroup E K` by the
equivalent condition `∀ M : FiniteIntermediateField E K.field,
a ∈ v.finiteIntermediateUnitNormRange E K M`. -/
def mem_infiniteUnitNormSubgroup_iffStatement
    (v : ValuationData D A) (E : ClosedSubgroup G)
    (K : FiniteAbstractField G)
    (a : ambientFixedAddSubgroup A K.field) : Prop :=
    a ∈ v.infiniteUnitNormSubgroup E K ↔
      ∀ M : FiniteIntermediateField E K.field,
        a ∈ v.finiteIntermediateUnitNormRange E K M

/-- Target: proves the bound
`v.infiniteUnitNormSubgroup E K ≤ infiniteNormSubgroup A E K.field`. -/
def infiniteUnitNormSubgroup_le_normSubgroupStatement
    (v : ValuationData D A) (E : ClosedSubgroup G)
    (K : FiniteAbstractField G) : Prop :=
    v.infiniteUnitNormSubgroup E K ≤ infiniteNormSubgroup A E K.field

end ValuationData

end

end Langlands.NYLL.ClassFormation
