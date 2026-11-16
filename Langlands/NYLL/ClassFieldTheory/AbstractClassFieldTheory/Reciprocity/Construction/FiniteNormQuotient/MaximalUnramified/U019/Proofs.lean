/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FiniteNormQuotient.MaximalUnramified.Statements

/-!
# NYLL M039.019: the maximal-unramified norm subgroup lies in a finite norm subgroup

Modified by Worker 5264, 15 November 2026, and Worker 743, 16 November 2026:
prove the target
`DegreeData.maximalUnramifiedNormSubgroup_le_finiteNormSubgroupStatement`
(M039.019) by the source proof of
`DegreeData.maximalUnramifiedNormSubgroup_le_finiteNormSubgroup` in
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FiniteNormQuotient.lean`
at fbd320cd8b1b06487c58227e92eb135794267709. Prefix the namespace with
`Langlands.NYLL`, give the theorem the target proposition as its type and
begin the proof with `show` stating it unfolded. The source's first rewrite,
with the `rfl` theorem `maximalUnramifiedNormSubgroup_eq_infiniteNormSubgroup`
(M029.025), whose proof is not published, is replaced by stating its
right-hand side in that `show`. The source's `iInf_le_of_le` step at the
field `D.fieldAsMaximalUnramifiedIntermediate K L hLK` (M039.018), which is
not yet in the Library, uses that definition's body instead: the structure
literal with field `L`, `above` the final step `inf_le_left` of the source
proof of `D.maximalUnramifiedField_le L` (M029.019, unpublished proof),
`below := hLK` and `finite := hfinite`. The remaining steps (`rw
[infiniteNormSubgroup]`, `rfl`) are the source's. Replace the source imports
by the target's statement module and omit the rest of the source file. See
the paired Markdown and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

open KummerTheory

noncomputable section

section quotientMaps

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- The defining intersection for the infinite norm subgroup is contained
in the norm image from the particular finite field `L`. -/
theorem maximalUnramifiedNormSubgroup_le_finiteNormSubgroup
    (D : DegreeData G) (A : Rep ℤ G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hfinite : Finite (K.toSubgroup ⧸ (L.toSubgroup.subgroupOf K.toSubgroup))] :
    maximalUnramifiedNormSubgroup_le_finiteNormSubgroupStatement D A K L hLK := by
  show infiniteNormSubgroup A (D.maximalUnramifiedField L) K ≤
    finiteNormSubgroup A K L hLK
  rw [infiniteNormSubgroup]
  refine iInf_le_of_le
    ({ field := L
       above := show (D.maximalUnramifiedField L).toSubgroup ≤ L.toSubgroup from
         inf_le_left
       below := hLK
       finite := hfinite } :
      FiniteIntermediateField (D.maximalUnramifiedField L) K) ?_
  rfl

end DegreeData

end quotientMaps

end

end Langlands.NYLL.ClassFormation
