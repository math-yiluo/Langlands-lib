/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.RelativeNorm.Statements
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.U014.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Norm.U002.Proofs

/-!
# NYLL M026.019: transitivity of relative norms in a finite tower

Modified by Worker 735, 16 November 2026: extract the theorem
`DegreeData.FiniteTower.norm_trans_apply` (M026.019) and the two source-private
theorems it uses, `relativeCosetAction_towerProductEquiv` (M026.017) and
`finiteTowerNormTransApplyAux` (M026.018), from
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/NormLaws.lean` at
fbd320cd8b1b06487c58227e92eb135794267709; prefix the namespace with
`Langlands.NYLL`, import the published statement module and the published
proofs of `relativeTowerQuotientFinite` (M026.014) and
`relativeCosetAction_mk` (M024.002) instead of the source imports, state
M026.019 through the published `norm_trans_applyStatement`, and keep M026.017
and M026.018 private. The unpublished source simp lemma
`relativeNorm_apply_coe` (M024.010) is proved locally as the private
definitional lemma `relativeNormApplyCoeLocal`, and the rewrites by the source
simp lemma `relativeCosetAction_mk` (M024.002) use its published proof
through the private restatement `relativeCosetActionMkLocal`. In M026.018 the
`letI` value `relativeTowerQuotientFinite K L M hML hLK` is given its unfolded
`Finite` type by `show ... from`. All other proof steps are the source ones.
See the paired Markdown and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
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

/-- Source-private M026.017: the coset action at the coset corresponding to
`(q, r)` under the tower decomposition is the action of a representative of
`q` on the coset action at `r`. -/
private theorem relativeCosetAction_towerProductEquiv
    (A : Rep ℤ G) (K L M : ClosedSubgroup G)
    (hML : M.toSubgroup ≤ L.toSubgroup)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (a : ambientFixedAddSubgroup A M)
    (q : K.toSubgroup ⧸ extensionSubgroup K L hLK)
    (r : L.toSubgroup ⧸ extensionSubgroup L M hML) :
    relativeCosetAction A K M (hML.trans hLK) a
        ((Subgroup.quotientTowerEquiv hML hLK).symm (q, r)) =
      A.ρ (Quotient.out q).1 (relativeCosetAction A L M hML a r) := by
  refine Quotient.inductionOn' r ?_
  intro x
  have he : (Subgroup.quotientTowerEquiv hML hLK).symm
      (q, QuotientGroup.mk x) =
      QuotientGroup.mk (Quotient.out q * Subgroup.inclusion hLK x) := rfl
  rw [he, relativeCosetActionMkLocal, relativeCosetActionMkLocal]
  change A.ρ ((Quotient.out q).1 * x.1) a.1 =
    A.ρ (Quotient.out q).1 (A.ρ x.1 a.1)
  rw [map_mul]
  rfl

/-- Source-private M026.018: transitivity of relative norms along
`M ≤ L ≤ K`, with the composite finiteness witness
`relativeTowerQuotientFinite`. -/
private theorem finiteTowerNormTransApplyAux
    (A : Rep ℤ G) (K L M : ClosedSubgroup G)
    (hML : M.toSubgroup ≤ L.toSubgroup)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    [Finite (L.toSubgroup ⧸ extensionSubgroup L M hML)]
    (a : ambientFixedAddSubgroup A M) :
    letI : Finite (K.toSubgroup ⧸ extensionSubgroup K M (hML.trans hLK)) :=
      show Finite (K.toSubgroup ⧸ extensionSubgroup K M (hML.trans hLK)) from
        relativeTowerQuotientFinite K L M hML hLK
    relativeNorm A K L hLK (relativeNorm A L M hML a) =
      relativeNorm A K M (hML.trans hLK) a := by
  apply Subtype.ext
  let := Fintype.ofFinite (K.toSubgroup ⧸ extensionSubgroup K L hLK)
  let := Fintype.ofFinite (L.toSubgroup ⧸ extensionSubgroup L M hML)
  let totalFintype : Fintype
      (K.toSubgroup ⧸ extensionSubgroup K M (hML.trans hLK)) :=
    Fintype.ofEquiv
      ((K.toSubgroup ⧸ extensionSubgroup K L hLK) ×
        (L.toSubgroup ⧸ extensionSubgroup L M hML))
      (Subgroup.quotientTowerEquiv hML hLK).symm
  have htotalFintype : Fintype.ofFinite
      (K.toSubgroup ⧸ extensionSubgroup K M (hML.trans hLK)) = totalFintype :=
    Subsingleton.elim _ _
  have houter : ∀ q : K.toSubgroup ⧸ extensionSubgroup K L hLK,
      relativeCosetAction A K L hLK (relativeNorm A L M hML a) q =
        A.ρ (Quotient.out q).1 (relativeNormValue A L M hML a) := by
    intro q
    calc
      relativeCosetAction A K L hLK (relativeNorm A L M hML a) q =
          relativeCosetAction A K L hLK (relativeNorm A L M hML a)
            (QuotientGroup.mk (Quotient.out q)) := by
              exact congrArg
                (relativeCosetAction A K L hLK (relativeNorm A L M hML a))
                (Quotient.out_eq' q).symm
      _ = A.ρ (Quotient.out q).1
          ((relativeNorm A L M hML a : ambientFixedAddSubgroup A L) : A.V) :=
        relativeCosetActionMkLocal A K L hLK (relativeNorm A L M hML a)
          (Quotient.out q)
      _ = A.ρ (Quotient.out q).1 (relativeNormValue A L M hML a) := by
        rw [relativeNormApplyCoeLocal]
  simp only [relativeNormApplyCoeLocal, relativeNormValue]
  rw [htotalFintype]
  rw [Finset.sum_congr rfl (fun q _ ↦ houter q)]
  simp only [relativeNormValue]
  simp_rw [map_sum]
  rw [← Fintype.sum_prod_type (f := fun p :
    (K.toSubgroup ⧸ extensionSubgroup K L hLK) ×
      (L.toSubgroup ⧸ extensionSubgroup L M hML) ↦
        A.ρ (Quotient.out p.1).1
          (relativeCosetAction A L M hML a p.2))]
  calc
    ∑ p : (K.toSubgroup ⧸ extensionSubgroup K L hLK) ×
        (L.toSubgroup ⧸ extensionSubgroup L M hML),
        A.ρ (Quotient.out p.1).1 (relativeCosetAction A L M hML a p.2) =
      ∑ p, relativeCosetAction A K M (hML.trans hLK) a
        ((Subgroup.quotientTowerEquiv hML hLK).symm p) := by
          apply Fintype.sum_congr
          intro p
          exact (relativeCosetAction_towerProductEquiv A K L M hML hLK a p.1 p.2).symm
    _ = ∑ q, relativeCosetAction A K M (hML.trans hLK) a q :=
      (Subgroup.quotientTowerEquiv hML hLK).symm.sum_comp
        (relativeCosetAction A K M (hML.trans hLK) a)

namespace DegreeData.FiniteTower

variable (T : DegreeData.FiniteTower G)

/-- Relative norms are transitive along a finite tower.  All containments and
finite quotient witnesses are obtained from `T`. -/
theorem norm_trans_apply (A : Rep ℤ G)
    (a : ambientFixedAddSubgroup A T.top) :
    norm_trans_applyStatement T A a := by
  exact finiteTowerNormTransApplyAux A T.base T.middle T.top
    T.top_le_middle T.middle_le_base a

end DegreeData.FiniteTower

end
end Langlands.NYLL.ClassFormation
