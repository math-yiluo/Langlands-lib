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
# NYLL M029.023: the subgroup of the maximal unramified field is normal

Modified by Worker 5264, 15 November 2026: prove the target
`DegreeData.extensionSubgroup_maximalUnramifiedField_normalStatement`
(M029.023) by the source proof of
`DegreeData.extensionSubgroup_maximalUnramifiedField_normal` in
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/NormSubgroup.lean`
at fbd320cd8b1b06487c58227e92eb135794267709. Prefix the namespace with
`Langlands.NYLL`, give the theorem the target proposition as its type and
begin the proof by unfolding it. The source proof rewrites with the theorem
`D.extensionSubgroup_maximalUnramifiedField K L hLK` (M029.022), whose proof
is not yet in the Library; this module proves that equation as the private
theorem `extensionSubgroup_maximalUnramifiedField_aux` by the source proof of
M029.022, in which the membership criteria M022.001, M010.016 and M029.018
are applied through local copies `hmemExt`, `hmemIn` and `hmemMax` (the last
proved by the published `mem_fieldInertia_iff`, M010.013). The final
`infer_instance` finds the published instance
`extensionInertiaWithin_normal`. Replace the source imports by the target's
statement module and the three published proof modules, and omit the unused
`open KummerTheory` and the rest of the source file. See the paired Markdown
and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.

Modified by Worker 743, 16 November 2026: status wording in this comment
only ("not yet in the Library").
-/

universe u

namespace Langlands.NYLL.ClassFormation

open CyclicCohomology

noncomputable section

section maximalUnramifiedFields

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- Inside `G_K`, the absolute subgroup of `\widetilde L` is the relative
inertia subgroup (the source theorem
`DegreeData.extensionSubgroup_maximalUnramifiedField`, M029.022, proved by its
source proof). -/
private theorem extensionSubgroup_maximalUnramifiedField_aux (D : DegreeData G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup) :
    extensionSubgroup K (D.maximalUnramifiedField L)
        ((show (D.maximalUnramifiedField L).toSubgroup ≤ L.toSubgroup from
          inf_le_left).trans hLK) =
      D.extensionInertiaWithin K L hLK := by
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

/-- The subgroup representing the maximal unramified field is normal in the base subgroup. -/
theorem extensionSubgroup_maximalUnramifiedField_normal (D : DegreeData G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L hLK).Normal] :
    extensionSubgroup_maximalUnramifiedField_normalStatement D K L hLK := by
  unfold extensionSubgroup_maximalUnramifiedField_normalStatement
  rw [extensionSubgroup_maximalUnramifiedField_aux D K L hLK]
  infer_instance

end DegreeData

end maximalUnramifiedFields

end

end Langlands.NYLL.ClassFormation
