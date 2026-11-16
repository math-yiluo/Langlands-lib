/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.NormSubgroup.Main.Definitions

/-!
# The lift out of the maximal-unramified norm quotient

Modified by Worker 5264, 15 November 2026: port the source definition
M029.035 `DegreeData.maximalUnramifiedNormQuotientLift` of
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/NormSubgroup.lean`
at fbd320cd8b1b06487c58227e92eb135794267709. Prefix the namespace with
`Langlands.NYLL` and replace the source imports by the published module of
the infinite and maximal-unramified norm quotients. The body applies the
theorem M029.026 `mem_maximalUnramifiedNormSubgroup_iff`, whose proof is not
published; it is replaced by the same equivalence stated with `show` and
proved by `Iff.rfl` (the source proof rewrites with the `rfl` theorem
M029.025, since `D.maximalUnramifiedNormSubgroup A K L` is by definition
`infiniteNormSubgroup A (D.maximalUnramifiedField L) K`). It occurs in a
proof argument, so by proof irrelevance the definition is the source one.
The docstring, the binders and the remaining body are unchanged. Omit the
rest of the source file. See the paired Markdown and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

open KummerTheory

open CyclicCohomology

noncomputable section

section maximalUnramifiedNorms

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- Descend an additive homomorphism that kills the maximal-unramified norm subgroup. -/
def maximalUnramifiedNormQuotientLift
    {B : Type*} [AddCommGroup B]
    (D : DegreeData G) (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (f : ambientFixedAddSubgroup A K →+ B)
    (hf : D.maximalUnramifiedNormSubgroup A K L ≤ f.ker) :
    D.MaximalUnramifiedNormQuotient A K L →+ B := by
  unfold MaximalUnramifiedNormQuotient
  refine infiniteNormQuotientLift A (D.maximalUnramifiedField L) K f ?_
  intro a ha
  exact hf ((show a ∈ D.maximalUnramifiedNormSubgroup A K L ↔
      a ∈ infiniteNormSubgroup A (D.maximalUnramifiedField L) K from
    Iff.rfl).2 ha)

end DegreeData

end maximalUnramifiedNorms

end
end Langlands.NYLL.ClassFormation
