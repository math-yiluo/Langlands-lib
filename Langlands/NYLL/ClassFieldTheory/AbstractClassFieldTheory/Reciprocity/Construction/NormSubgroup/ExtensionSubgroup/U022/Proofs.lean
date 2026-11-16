/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.NormSubgroup.ExtensionSubgroup.Statements
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.U013.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.U016.Proofs
import Langlands.NYLL.GaloisCohomology.Kummer.Abstract.KummerAbelianAssembly.U001.U001.Proofs

/-!
# NYLL M029.022: the subgroup of the maximal unramified field inside `G_K`

Modified by Worker 5264, 15 November 2026: prove the target
`DegreeData.extensionSubgroup_maximalUnramifiedFieldStatement` (M029.022) by
the source proof of `DegreeData.extensionSubgroup_maximalUnramifiedField` in
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/NormSubgroup.lean`
at fbd320cd8b1b06487c58227e92eb135794267709. Prefix the namespace with
`Langlands.NYLL`, give the theorem the target proposition as its type and
begin the proof by unfolding it. The source proof applies the membership
criteria `mem_extensionSubgroup_iff` (M022.001), `mem_fieldInertiaWithin_iff`
(M010.016), both published with `...Statement` types, and
`mem_maximalUnramifiedField_iff` (M029.018), whose proof is not published;
this module applies local copies `hmemExt`, `hmemIn` and `hmemMax` of them,
the last proved by the published `mem_fieldInertia_iff` (M010.013), which is
the source proof of M029.018 after its `rfl` rewrite
`maximalUnramifiedField_eq_fieldInertia` (M029.017). The proof argument
`D.maximalUnramifiedField_le_of_le hLK` of the source is the target's
`(show ... from inf_le_left).trans hLK`. Replace the source imports by the
target's statement module and the three published proof modules, and omit
the unused `open KummerTheory` and the rest of the source file. See the
paired Markdown and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

universe u

namespace Langlands.NYLL.ClassFormation

open CyclicCohomology

noncomputable section

section maximalUnramifiedFields

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- Inside `G_K`, the absolute subgroup of `\widetilde L` is the relative
inertia subgroup. -/
theorem extensionSubgroup_maximalUnramifiedField (D : DegreeData G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup) :
    extensionSubgroup_maximalUnramifiedFieldStatement D K L hLK := by
  unfold extensionSubgroup_maximalUnramifiedFieldStatement
  have hmemExt : ∀ (M : ClosedSubgroup G) (hMK : M.toSubgroup ≤ K.toSubgroup)
      (k : K.toSubgroup), k ∈ extensionSubgroup K M hMK ↔ (k : G) ∈ M :=
    fun M hMK k => KummerTheory.mem_extensionSubgroup_iff K M hMK k
  have hmemMax : ∀ g : G,
      g ∈ D.maximalUnramifiedField L ↔ g ∈ L ∧ D.degree g = 1 :=
    fun g => D.mem_fieldInertia_iff L g
  have hmemIn : ∀ k : K.toSubgroup,
      k ∈ D.fieldInertiaWithin K ↔ D.degree k.1 = 1 :=
    fun k => D.mem_fieldInertiaWithin_iff K k
  ext k
  constructor
  · intro hk
    have hkMax : k.1 ∈ D.maximalUnramifiedField L :=
      (hmemExt (D.maximalUnramifiedField L) _ k).1 hk
    have hkData := (hmemMax k.1).1 hkMax
    exact ⟨(hmemExt L hLK k).2 hkData.1, (hmemIn k).2 hkData.2⟩
  · intro hk
    apply (hmemExt (D.maximalUnramifiedField L) _ k).2
    apply (hmemMax k.1).2
    exact ⟨(hmemExt L hLK k).1 hk.1, (hmemIn k).1 hk.2⟩

end DegreeData

end maximalUnramifiedFields

end

end Langlands.NYLL.ClassFormation
