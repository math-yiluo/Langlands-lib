/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.RelativeNorm.Statements
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.U012.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Norm.U002.Proofs

/-!
# NYLL M026.013: invariance of the relative norm under the normal-extension action

Modified by Worker 735, 16 November 2026: extract the theorem
`relativeNorm_normalExtensionAction` (M026.013) from
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/NormLaws.lean` at
fbd320cd8b1b06487c58227e92eb135794267709; prefix the namespace with
`Langlands.NYLL`, import the published statement module and the published
proofs of `normalExtensionAction_coe` (M026.012) and `relativeCosetAction_mk`
(M024.002) instead of the source imports, state the theorem through the
published `relativeNorm_normalExtensionActionStatement` with its normality and
finiteness binders written, as in that statement, through the
`Subgroup.subgroupOf` body of `extensionSubgroup K L hLK`, and open the proof
with a `show` of the unfolded statement. The source uses of the simp lemmas
`relativeCosetAction_mk` and `normalExtensionAction_coe` use their published
proofs through the private restatements `relativeCosetActionMkLocal` and
`normalExtensionActionCoeLocal`, and the unpublished source simp lemma
`relativeNorm_apply_coe` (M024.010) is proved locally, by `rfl`, as the
private lemma `relativeNormApplyCoeLocal`. All other proof steps are the
source ones. See the paired Markdown and `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

open KummerTheory

open CyclicCohomology

noncomputable section

open scoped BigOperators Pointwise

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/-- Local copy of the unpublished source simp lemma `relativeNorm_apply_coe`
(M024.010): the coercion of a relative norm is its defining coset sum. -/
private theorem relativeNormApplyCoeLocal
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (a : ambientFixedAddSubgroup A L) :
    ((relativeNorm A K L hLK a : ambientFixedAddSubgroup A K) : A.V) =
      relativeNormValue A K L hLK a :=
  rfl

/-- The published `relativeCosetAction_mk` (M024.002) with its statement
unfolded, for use in rewriting. -/
private theorem relativeCosetActionMkLocal
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (a : ambientFixedAddSubgroup A L) (k : K.toSubgroup) :
    relativeCosetAction A K L hLK a (QuotientGroup.mk k) = A.ρ k.1 a.1 :=
  relativeCosetAction_mk A K L hLK a k

/-- The published `normalExtensionAction_coe` (M026.012) with its statement
unfolded, for use in rewriting. -/
private theorem normalExtensionActionCoeLocal
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    (k : K.toSubgroup) (a : ambientFixedAddSubgroup A L) :
    ((normalExtensionAction A K L hLK hnormal k a : ambientFixedAddSubgroup A L) : A.V) =
      A.ρ k.1 a.1 :=
  normalExtensionAction_coe A K L hLK hnormal k a

/-- For a finite Galois abstract extension, the relative norm is invariant under
the `G_K`-conjugacy action on `A_L`. -/
theorem relativeNorm_normalExtensionAction
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal)
    [Finite (K.toSubgroup ⧸ (L.toSubgroup.subgroupOf K.toSubgroup))]
    (k : K.toSubgroup) (a : ambientFixedAddSubgroup A L) :
    relativeNorm_normalExtensionActionStatement A K L hLK hnormal k a := by
  show relativeNorm A K L hLK (normalExtensionAction A K L hLK hnormal k a) =
      relativeNorm A K L hLK a
  apply Subtype.ext
  let := Fintype.ofFinite (K.toSubgroup ⧸ extensionSubgroup K L hLK)
  let e : (K.toSubgroup ⧸ extensionSubgroup K L hLK) ≃
      (K.toSubgroup ⧸ extensionSubgroup K L hLK) :=
    Equiv.mulRight (QuotientGroup.mk k)
  have hterm : ∀ q : K.toSubgroup ⧸ extensionSubgroup K L hLK,
      relativeCosetAction A K L hLK (normalExtensionAction A K L hLK hnormal k a) q =
        relativeCosetAction A K L hLK a (e q) := by
    intro q
    refine Quotient.inductionOn' q ?_
    intro x
    simp only [relativeCosetActionMkLocal, normalExtensionActionCoeLocal]
    have he : e (QuotientGroup.mk x) = QuotientGroup.mk (x * k) := rfl
    rw [he, relativeCosetActionMkLocal]
    change A.ρ x.1 (A.ρ k.1 a.1) = A.ρ (x.1 * k.1) a.1
    rw [map_mul]
    rfl
  simp only [relativeNormApplyCoeLocal, relativeNormValue]
  simp_rw [hterm]
  exact e.sum_comp (relativeCosetAction A K L hLK a)

end
end Langlands.NYLL.ClassFormation
