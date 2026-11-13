/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FieldRepresentation.Action.U004.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.PrimeElements.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Norm.U002.Proofs
import Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic

/-!
# NYLL fixed coefficients as cyclic cycles

Modified by Worker 196, 13 November 2026: extract M074.001, lines 33–115,
from `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/CyclicNormQuotient.lean`
at `fbd320cd8b1b06487c58227e92eb135794267709`. Prefix the namespace with
`Langlands.NYLL`, use focused published imports, and expand `extensionSubgroup`
to its Mathlib definition. Replace the source cyclicity helper by the Mathlib
cyclicity and subgroup-top equivalences. Preserve the full telescope and actual
construction, including its proof terms. See the paired Markdown and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

open KummerTheory CyclicCohomology CategoryTheory
noncomputable section

variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/-- The actual fixed group `A_K` is the kernel of `ρ(g)-1` on `A_L`
when `g` generates `G(L/K)`. -/
def cyclicFixedCycleEquiv
    (A : Rep ℤ G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal)
    (hfinite : Finite (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup))
    (g : K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
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
    ambientFixedAddSubgroup A K ≃+
      T.moduleCatLeftHomologyData.K := by
  intro instNormal instFinite instFintype instCyclic instCommGroup M T
  let toCycle : ambientFixedAddSubgroup A K →
      T.moduleCatLeftHomologyData.K := fun a => by
    let aL := fixedFieldInclusion A K L hLK a
    let aM : M.V :=
      (extensionFixedRepresentationEquiv A K L hLK hnormal).symm aL
    refine ⟨aM, sub_eq_zero.mpr ?_⟩
    refine Quotient.inductionOn' g ?_
    intro k
    apply Subtype.ext
    change A.ρ k.1 a.1 = a.1
    exact a.2 k
  let fromCycle : T.moduleCatLeftHomologyData.K →
      ambientFixedAddSubgroup A K := fun x => by
    let aM : M.V := x.1
    let aL : ambientFixedAddSubgroup A L :=
      extensionFixedRepresentationEquiv A K L hLK hnormal aM
    have hxzero : T.g.hom aM = 0 := x.2
    have hxg : M.ρ g aM = aM := by
      apply sub_eq_zero.mp
      exact hxzero
    have hxall : ∀ q, M.ρ q aM = aM := by
      let : Module ℤ M := M.hV2
      exact (Representation.mem_invariants_iff_of_forall_mem_zpowers
        M.ρ g hg aM).2 hxg
    refine ⟨aL.1, ?_⟩
    intro k
    have hk := hxall
      ((QuotientGroup.mk' (L.toSubgroup.subgroupOf K.toSubgroup)) k)
    have haction := extensionFixedRepresentation_action_coe
      A K L hLK hnormal
      ((QuotientGroup.mk' (L.toSubgroup.subgroupOf K.toSubgroup)) k) aM
    have haction' :
        (M.ρ ((QuotientGroup.mk'
          (L.toSubgroup.subgroupOf K.toSubgroup)) k) aM).1 =
          A.ρ k.1 aL.1 := by
      calc
        _ = relativeCosetAction A K L hLK aL
              ((QuotientGroup.mk'
                (L.toSubgroup.subgroupOf K.toSubgroup)) k) := haction
        _ = A.ρ k.1 aL.1 :=
          relativeCosetAction_mk A K L hLK aL k
    exact haction'.symm.trans ((congrArg Subtype.val hk).trans rfl)
  exact
    { toFun := toCycle
      invFun := fromCycle
      left_inv := by
        intro a
        apply Subtype.ext
        rfl
      right_inv := by
        intro x
        apply Subtype.ext
        rfl
      map_add' := by
        intro a b
        apply Subtype.ext
        apply Subtype.ext
        rfl }

end
end Langlands.NYLL.ClassFormation
