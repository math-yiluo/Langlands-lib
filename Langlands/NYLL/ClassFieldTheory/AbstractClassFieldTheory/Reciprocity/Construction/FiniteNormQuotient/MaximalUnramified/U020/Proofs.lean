/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FiniteNormQuotient.MaximalUnramified.Statements
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FiniteNormQuotient.U012.Proofs

/-!
# NYLL M039.020: the maximal-unramified norm subgroup lies in the finite norm-class kernel

Modified by Worker 5264, 15 November 2026, and Worker 743, 16 November 2026:
prove the target
`Langlands.NYLL.PortInternal.M039.d020Statement` (M039.020) by the source
proof of the private theorem
`DegreeData.maximalUnramifiedNormSubgroup_le_finiteNormClassHom_ker` in
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FiniteNormQuotient.lean`
at fbd320cd8b1b06487c58227e92eb135794267709, under the stable name
`Langlands.NYLL.PortInternal.M039.d020`. Give the theorem the target
proposition as its type and begin the proof with `show` stating it
unfolded. The source proof applies `finiteNormClass_eq_zero_iff` (M039.012)
and `maximalUnramifiedNormSubgroup_le_finiteNormSubgroup` (M039.019), whose
proofs are not yet in the Library; this module proves them as the private
theorems `finiteNormClass_eq_zero_iff` and
`maximalUnramifiedNormSubgroup_le_finiteNormSubgroup_aux` by their source
proofs (in the latter the `rfl` rewrite with the unpublished M029.025 is
replaced by `show`, and the field
`D.fieldAsMaximalUnramifiedIntermediate K L hLK` (M039.018), not yet in the
Library, by its body: the structure literal with field `L`, `above` the
final step `inf_le_left` of the source proof of M029.019, `below := hLK` and
`finite := hfinite`). Replace the source imports by the target's statement
module and omit the rest of the source file. See the paired Markdown and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

/-! Integrator, 16 November 2026: reuse the independently accepted public
M039.012 proof and remove the corresponding private copies.
The preceding dated port account describes the original submission. -/

namespace Langlands.NYLL.ClassFormation

open KummerTheory

noncomputable section

section quotientMaps

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- The defining intersection for the infinite norm subgroup is contained
in the norm image from the particular finite field `L` (the source theorem
`DegreeData.maximalUnramifiedNormSubgroup_le_finiteNormSubgroup`, M039.019,
proved by its source proof). -/
private theorem maximalUnramifiedNormSubgroup_le_finiteNormSubgroup_aux
    (D : DegreeData G) (A : Rep ℤ G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hfinite : Finite (K.toSubgroup ⧸ (L.toSubgroup.subgroupOf K.toSubgroup))] :
    D.maximalUnramifiedNormSubgroup A K L ≤
      finiteNormSubgroup A K L hLK := by
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

/-- The private source theorem
`DegreeData.maximalUnramifiedNormSubgroup_le_finiteNormClassHom_ker`: the
maximal-unramified norm subgroup lies in the kernel of the finite norm class
map. -/
theorem _root_.Langlands.NYLL.PortInternal.M039.d020
    (D : DegreeData G) (A : Rep ℤ G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hfinite : Finite (K.toSubgroup ⧸ (L.toSubgroup.subgroupOf K.toSubgroup))] :
    Langlands.NYLL.PortInternal.M039.d020Statement D A K L hLK := by
  show D.maximalUnramifiedNormSubgroup A K L ≤
    (finiteNormClassHom A K L hLK).ker
  intro a ha
  exact (finiteNormClass_eq_zero_iff A K L hLK a).2
    (maximalUnramifiedNormSubgroup_le_finiteNormSubgroup_aux D A K L hLK ha)

end DegreeData

end quotientMaps

end

end Langlands.NYLL.ClassFormation
