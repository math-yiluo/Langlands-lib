/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.PrimeElements.RelativeNorm.Statements
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Norm.U002.Proofs
import Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.PrimeElements.U002.Proofs

/-!
# NYLL M028.003: the relative norm of an included fixed element

Modified by Worker 735, 16 November 2026: extract the theorem
`relativeNorm_fixedFieldInclusion` (M028.003) from
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/PrimeElements.lean` at
fbd320cd8b1b06487c58227e92eb135794267709; prefix the namespace with
`Langlands.NYLL`, import the published statement module and the published
proofs of `relativeCosetAction_mk` (M024.002) and `fixedFieldInclusion_coe`
(M028.002) and the published module defining `extensionSubgroup` instead of
the source import, state the theorem through the
published `relativeNorm_fixedFieldInclusionStatement`, and open the proof with
a `show` of the unfolded statement. The source rewrites by the simp lemmas
`relativeCosetAction_mk` and `fixedFieldInclusion_coe` use their published
proofs through the private restatements `relativeCosetActionMkLocal` and
`fixedFieldInclusionCoeLocal`; the unpublished source lemmas
`relativeNorm_apply_coe` (M024.010) and
`DegreeData.FiniteAbstractExtension.extensionSubgroup_index_eq_degree`
(M010.092) are proved locally, by `rfl`, as the private lemmas
`relativeNormApplyCoeLocal` and `extensionSubgroupIndexEqDegreeLocal`. All
other proof steps are the source ones. See the paired Markdown and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
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

/-- The published `fixedFieldInclusion_coe` (M028.002) with its statement
unfolded, for use in rewriting. -/
private theorem fixedFieldInclusionCoeLocal
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (a : ambientFixedAddSubgroup A K) :
    ((fixedFieldInclusion A K L hLK a : ambientFixedAddSubgroup A L) : A.V) = a.1 :=
  fixedFieldInclusion_coe A K L hLK a

/-- Local copy of the unpublished source simp lemma
`DegreeData.FiniteAbstractExtension.extensionSubgroup_index_eq_degree`
(M010.092): the index of the represented extension subgroup is the degree. -/
private theorem extensionSubgroupIndexEqDegreeLocal
    (E : DegreeData.FiniteAbstractExtension G) :
    (extensionSubgroup E.base E.field E.below).index = (E.degree : ℕ) :=
  rfl

/-- The norm of an element already fixed over `K` is its `[L:K]`-fold sum. -/
theorem relativeNorm_fixedFieldInclusion
    (A : Rep ℤ G) (E : DegreeData.FiniteAbstractExtension G)
    (a : ambientFixedAddSubgroup A E.base) :
    relativeNorm_fixedFieldInclusionStatement A E a := by
  show relativeNorm A E.base E.field E.below
      (fixedFieldInclusion A E.base E.field E.below a) = (E.degree : ℕ) • a
  apply Subtype.ext
  let := Fintype.ofFinite
    (E.base.toSubgroup ⧸ extensionSubgroup E.base E.field E.below)
  have hterm : ∀ q : E.base.toSubgroup ⧸
      extensionSubgroup E.base E.field E.below,
      relativeCosetAction A E.base E.field E.below
        (fixedFieldInclusion A E.base E.field E.below a) q = a.1 := by
    intro q
    refine Quotient.inductionOn' q ?_
    intro k
    rw [relativeCosetActionMkLocal, fixedFieldInclusionCoeLocal]
    exact a.2 k
  simp only [relativeNormApplyCoeLocal, relativeNormValue]
  simp_rw [hterm]
  rw [Finset.sum_const, Finset.card_univ]
  change Fintype.card
      (E.base.toSubgroup ⧸ extensionSubgroup E.base E.field E.below) • a.1 =
    (E.degree : ℕ) • a.1
  rw [← extensionSubgroupIndexEqDegreeLocal E,
    Subgroup.index, Nat.card_eq_fintype_card]

end
end Langlands.NYLL.ClassFormation
