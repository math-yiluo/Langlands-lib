/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.PrimeElements.RelativeNorm.Statements
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Norm.U002.Proofs
import Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions

/-!
# NYLL M028.004: the relative norm of the trivial extension

Modified by Worker 735, 16 November 2026: extract the theorem
`relativeNorm_self` (M028.004) from
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/PrimeElements.lean` at
fbd320cd8b1b06487c58227e92eb135794267709; prefix the namespace with
`Langlands.NYLL`, import the published statement module and the published
proof of `relativeCosetAction_mk` (M024.002) instead of the source import,
import the published module defining `extensionSubgroup`, state the theorem
through the published `relativeNorm_selfStatement` with its finiteness binder
written, as in that statement, through the `Subgroup.subgroupOf` body of
`extensionSubgroup K K le_rfl`, omit the source `@[simp]` attribute (the
conclusion is an opaque proposition), and open the proof with a `show` of the
unfolded statement. The source rewrite by the
simp lemma `relativeCosetAction_mk` uses its published proof through the
private restatement `relativeCosetActionMkLocal`, and the unpublished source
lemma `relativeNorm_apply_coe` (M024.010) is proved locally, by `rfl`, as the
private lemma `relativeNormApplyCoeLocal`. All other proof steps are the
source ones. See the paired Markdown and `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

open KummerTheory

open CyclicCohomology

noncomputable section

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

/-- The norm of the trivial extension is the identity. -/
theorem relativeNorm_self
    (A : Rep ℤ G) (K : ClosedSubgroup G)
    [Finite (K.toSubgroup ⧸ (K.toSubgroup.subgroupOf K.toSubgroup))]
    (a : ambientFixedAddSubgroup A K) :
    relativeNorm_selfStatement A K a := by
  show relativeNorm A K K le_rfl a = a
  apply Subtype.ext
  let := Fintype.ofFinite
    (K.toSubgroup ⧸ extensionSubgroup K K le_rfl)
  have hterm : ∀ q : K.toSubgroup ⧸ extensionSubgroup K K le_rfl,
      relativeCosetAction A K K le_rfl a q = a.1 := by
    intro q
    refine Quotient.inductionOn' q ?_
    intro k
    rw [relativeCosetActionMkLocal]
    exact a.2 k
  simp only [relativeNormApplyCoeLocal, relativeNormValue]
  simp_rw [hterm]
  rw [Finset.sum_const, Finset.card_univ]
  have htop : extensionSubgroup K K le_rfl = ⊤ := by
    change K.toSubgroup.subgroupOf K.toSubgroup = ⊤
    exact Subgroup.subgroupOf_self _
  have hcard :
      Fintype.card (K.toSubgroup ⧸ extensionSubgroup K K le_rfl) = 1 := by
    rw [← Nat.card_eq_fintype_card,
      ← Subgroup.index_eq_card (extensionSubgroup K K le_rfl),
      htop, Subgroup.index_top]
  rw [hcard, one_nsmul]

end
end Langlands.NYLL.ClassFormation
