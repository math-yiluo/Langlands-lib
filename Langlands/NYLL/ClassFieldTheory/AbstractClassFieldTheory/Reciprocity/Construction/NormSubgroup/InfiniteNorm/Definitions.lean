/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.NormSubgroup.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Norm.RelativeNorm.Definitions

/-!
# NYLL M029: the infinite norm subgroup and the maximal-unramified norm subgroup

Modified by Worker 5264, 14 November 2026: extract M029.003, M029.004 and
M029.024 from the pinned NYLL NormSubgroup.lean at
fbd320cd8b1b06487c58227e92eb135794267709, prefix the namespace with
Langlands.NYLL and use focused published imports. Omit every other
declaration of the source file. The declarations, binders, universes and
bodies are otherwise unchanged. See the paired Markdown and
licenses/NYLL/LICENSE and NOTICE.
-/

namespace Langlands.NYLL.ClassFormation

open KummerTheory

open CyclicCohomology

noncomputable section

section infiniteNorms

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/-- The norm image from a finite intermediate field `M` to `K`. -/
def finiteIntermediateNormRange
    (A : Rep ℤ G) (E K : ClosedSubgroup G)
    (M : FiniteIntermediateField E K) :
    AddSubgroup (ambientFixedAddSubgroup A K) := by
  letI := M.finite
  exact (relativeNorm A K M.field M.below).range

/-- The norm subgroup for a possibly infinite extension:
`N_{E|K} A_E = ⋂_M N_{M|K} A_M`, where `M` runs through the finite
intermediate fields. -/
def infiniteNormSubgroup
    (A : Rep ℤ G) (E K : ClosedSubgroup G) :
    AddSubgroup (ambientFixedAddSubgroup A K) :=
  ⨅ M : FiniteIntermediateField E K,
    finiteIntermediateNormRange A E K M

end infiniteNorms

section maximalUnramifiedNorms

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- `N_{\widetilde L|K} A_{\widetilde L}` in the reciprocity construction. -/
def maximalUnramifiedNormSubgroup (D : DegreeData G) (A : Rep ℤ G)
    (K L : ClosedSubgroup G) :
    AddSubgroup (ambientFixedAddSubgroup A K) :=
  infiniteNormSubgroup A (D.maximalUnramifiedField L) K

end DegreeData

end maximalUnramifiedNorms

end
end Langlands.NYLL.ClassFormation
