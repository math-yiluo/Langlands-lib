/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.CyclicNormQuotient.NormClass.Definitions

/-!
# NYLL cyclic norm-class evaluation and surjectivity statements

Modified by Worker 196, 13 November 2026: extract the exact theorem types of
M074.003, lines 147–167, and M074.006, lines 269–285, from
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/CyclicNormQuotient.lean`
at `fbd320cd8b1b06487c58227e92eb135794267709`. Prefix the namespace with
`Langlands.NYLL`, append `Statement`, and make each theorem type the body of a
Prop-valued definition. Omit theorem proofs and attributes. Expand
`extensionSubgroup` to its Mathlib definition and replace the generator-cyclicity
helper by its Mathlib equivalent. Keep every source binder and local instance.
See the paired Markdown and `licenses/NYLL/`.
-/

namespace Langlands.NYLL.ClassFormation

open KummerTheory CyclicCohomology CategoryTheory
noncomputable section
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

def cyclicNormClassHom_applyStatement
    (A : Rep ℤ G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal)
    (hfinite : Finite (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup))
    (g : K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)
    (hg : ∀ x, x ∈ Subgroup.zpowers g)
    (a : ambientFixedAddSubgroup A K) : Prop :=
    let _ : (L.toSubgroup.subgroupOf K.toSubgroup).Normal := hnormal
    let _ : Finite (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup) := hfinite
    let _ : Fintype (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup) :=
      Fintype.ofFinite (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)
    let _ : IsCyclic (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup) :=
      isCyclic_iff_exists_zpowers_eq_top.mpr
        ⟨g, (Subgroup.eq_top_iff' _).mpr hg⟩
    let _ : CommGroup (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup) :=
      IsCyclic.commGroup
    let M := extensionFixedRepresentation A K L hLK hnormal
    let T := Rep.FiniteCyclicGroup.normHomCompSub M g
    cyclicNormClassHom A K L hLK hnormal hfinite g hg a =
      T.moduleCatLeftHomologyData.π
        (cyclicFixedCycleEquiv A K L hLK hnormal hfinite g hg a)

def cyclicNormClassHom_surjectiveStatement
    (A : Rep ℤ G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal)
    (hfinite : Finite (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup))
    (g : K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) : Prop :=
    let _ : (L.toSubgroup.subgroupOf K.toSubgroup).Normal := hnormal
    let _ : Finite (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup) := hfinite
    let _ : Fintype (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup) :=
      Fintype.ofFinite (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)
    let _ : IsCyclic (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup) :=
      isCyclic_iff_exists_zpowers_eq_top.mpr
        ⟨g, (Subgroup.eq_top_iff' _).mpr hg⟩
    let _ : CommGroup (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup) :=
      IsCyclic.commGroup
    Function.Surjective
      (cyclicNormClassHom A K L hLK hnormal hfinite g hg)

end
end Langlands.NYLL.ClassFormation
