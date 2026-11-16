/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 746, 16 November 2026 UTC:
Extract only the proof of M075.029
`abstractReciprocity_valuationAt_fixedFieldInclusion_of_totallyRamified` from
Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Core.lean at
fbd320cd8b1b06487c58227e92eb135794267709. Prefix the namespace with
`Langlands.NYLL`, state the theorem as the published Statement applied to the
source parameters, and import the published statement module together with
the published modules and proofs listed in the paired Markdown. The source
proof cites the unpublished M010.097
`FiniteAbstractExtension.residueDegree_eq_one_of_isTotallyRamified`, M027.007
`ValuationData.normalizedValuation_tower` and M028.003
`relativeNorm_fixedFieldInclusion`; they are replaced by private theorems with
their source proofs, together with the unpublished source chain behind
M027.007 (M011.017 with M010.103, M025.023 and M026.019 with the
source-private M026.017 and M026.018). These private theorems are taken from
Worker 5264's unreviewed shared draft (revision 1) of Task 7030:
`extensionSubgroup K L hLK` is written as its abbreviation body, the `rfl`
lemmas M010.093, M024.002, M024.010 and M028.002 are replaced by
`change`, `show` and `rfl` steps, M010.092 is the local fact `hindex`, and
M026.018 is applied directly instead of M026.019. The original LICENSE and
NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Core.TotallyRamifiedValuation.Statements
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteTower.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteAbstractField.Extension.NumericDefinitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteResidueExtension.ResidueDegreeDefinitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.U005.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.AbstractExtension.U036.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteResidue.U027.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.U014.Proofs
import Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.U005.Proofs
import Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.Divide.U017.Proofs

/-!
# Valuations along a finite totally ramified extension

The exact proof of M075.029: in a finite totally ramified extension `L | K`,
the normalized valuation of an element of `A_K`, viewed in `A_L`, is `[L : K]`
times its valuation in `A_K`.
-/

namespace Langlands.NYLL.ClassFormation

open KummerTheory

open CyclicCohomology

open scoped BigOperators

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace DegreeData

namespace FiniteAbstractExtension

variable (E : FiniteAbstractExtension G)

/-- The source proof of M010.097
`FiniteAbstractExtension.residueDegree_eq_one_of_isTotallyRamified` (not yet
published), with the `rfl` lemma M010.093 `mapped_relIndex_eq_residueDegree`
replaced by `change`: a totally ramified finite extension has residue degree
one. -/
private theorem residueDegree_eq_one_of_isTotallyRamified_aux
    (D : DegreeData G) (hE : E.IsTotallyRamified D) :
    (E.residueDegree D : ℕ) = 1 := by
  change (E.field.toSubgroup.map D.degree.toMonoidHom).relIndex
      (E.base.toSubgroup.map D.degree.toMonoidHom) = 1
  rw [Subgroup.relIndex_eq_one]
  exact hE

/-- The source proof of M010.103
`FiniteAbstractExtension.relativeResidueDegreeCardinal_eq_coe` (not yet
published): for a finite extension, the cardinal-valued relative residue
degree is the cardinal cast of the positive natural residue degree. -/
private theorem relativeResidueDegreeCardinal_eq_coe_aux
    (D : DegreeData G) :
    E.toAbstractExtension.relativeResidueDegreeCardinal D =
      ((E.residueDegree D : ℕ) : Cardinal) := by
  change Cardinal.mk
    (↥(E.base.toSubgroup.map D.degree.toMonoidHom) ⧸
      (E.field.toSubgroup.map D.degree.toMonoidHom).subgroupOf
        (E.base.toSubgroup.map D.degree.toMonoidHom)) =
      (Nat.card
        (↥(E.base.toSubgroup.map D.degree.toMonoidHom) ⧸
          (E.field.toSubgroup.map D.degree.toMonoidHom).subgroupOf
            (E.base.toSubgroup.map D.degree.toMonoidHom)) : Cardinal)
  exact (Nat.cast_card).symm

end FiniteAbstractExtension

/-- The source proof of M011.017
`FiniteResidueAbstractExtension.residueDegree_mul_absoluteResidueDegree`
(not yet published): for a finite extension, its positive residue degree
times the absolute residue degree of the base is the absolute residue degree
of the field. -/
private theorem residueDegree_mul_absoluteResidueDegree_aux
    (D : DegreeData G) (E : FiniteResidueAbstractExtension D) :
    (E.residueDegree : ℕ) * (E.base.residueDegree : ℕ) =
      (E.field.residueDegree : ℕ) := by
  have h :=
    AbstractExtension.relativeResidueDegreeCardinal_mul_residueDegreeCardinal
      E.toFiniteAbstractExtension.toAbstractExtension D
  change E.toFiniteAbstractExtension.toAbstractExtension.relativeResidueDegreeCardinal D *
      D.residueDegreeCardinal E.base.field =
    D.residueDegreeCardinal E.field.field at h
  rw [FiniteAbstractExtension.relativeResidueDegreeCardinal_eq_coe_aux
    E.toFiniteAbstractExtension D] at h
  change ((E.residueDegree : ℕ) : Cardinal) *
      D.residueDegreeCardinal E.base.field =
    D.residueDegreeCardinal E.field.field at h
  have hbase : D.residueDegreeCardinal E.base.field =
      ((E.base.residueDegree : ℕ) : Cardinal) :=
    E.base.residueDegreeCardinal_eq_coe
  have hfield : D.residueDegreeCardinal E.field.field =
      ((E.field.residueDegree : ℕ) : Cardinal) :=
    E.field.residueDegreeCardinal_eq_coe
  rw [hbase, hfield] at h
  exact_mod_cast h

end DegreeData

/-- The source proof of M028.003 `relativeNorm_fixedFieldInclusion` (not yet
published): the norm of an element already fixed over `K` is its `[L:K]`-fold
sum. The `rfl` lemmas M024.002 `relativeCosetAction_mk`, M028.002
`fixedFieldInclusion_coe` and M024.010 `relativeNorm_apply_coe` are replaced
by `change` steps, and the source lemma M010.092
`extensionSubgroup_index_eq_degree` is the local fact `hindex`. -/
private theorem relativeNorm_fixedFieldInclusion_aux
    (A : Rep ℤ G) (E : DegreeData.FiniteAbstractExtension G)
    (a : ambientFixedAddSubgroup A E.base) :
    relativeNorm A E.base E.field E.below
        (fixedFieldInclusion A E.base E.field E.below a) =
      (E.degree : ℕ) • a := by
  apply Subtype.ext
  let := Fintype.ofFinite
    (E.base.toSubgroup ⧸ E.field.toSubgroup.subgroupOf E.base.toSubgroup)
  have hterm : ∀ q : E.base.toSubgroup ⧸
      E.field.toSubgroup.subgroupOf E.base.toSubgroup,
      relativeCosetAction A E.base E.field E.below
        (fixedFieldInclusion A E.base E.field E.below a) q = a.1 := by
    intro q
    refine Quotient.inductionOn' q ?_
    intro k
    change A.ρ k.1 a.1 = a.1
    exact a.2 k
  change relativeNormValue A E.base E.field E.below
      (fixedFieldInclusion A E.base E.field E.below a) = _
  simp only [relativeNormValue]
  simp_rw [hterm]
  rw [Finset.sum_const, Finset.card_univ]
  change Fintype.card
      (E.base.toSubgroup ⧸ E.field.toSubgroup.subgroupOf E.base.toSubgroup) • a.1 =
    (E.degree : ℕ) • a.1
  have hindex :
      (E.field.toSubgroup.subgroupOf E.base.toSubgroup).index = (E.degree : ℕ) := by
    rw [Subgroup.index]
    rfl
  rw [← hindex, Subgroup.index, Nat.card_eq_fintype_card]

/-- The source proof of the source-private M026.017
`relativeCosetAction_towerProductEquiv`: the relative coset action at the
tower-product coset `(q, r)` is the action of a representative of `q` on the
relative coset action at `r`. -/
private theorem relativeCosetAction_towerProductEquiv_aux
    (A : Rep ℤ G) (K L M : ClosedSubgroup G)
    (hML : M.toSubgroup ≤ L.toSubgroup)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (a : ambientFixedAddSubgroup A M)
    (q : K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)
    (r : L.toSubgroup ⧸ M.toSubgroup.subgroupOf L.toSubgroup) :
    relativeCosetAction A K M (hML.trans hLK) a
        ((Subgroup.quotientTowerEquiv hML hLK).symm (q, r)) =
      A.ρ (Quotient.out q).1 (relativeCosetAction A L M hML a r) := by
  refine Quotient.inductionOn' r ?_
  intro x
  have he : (Subgroup.quotientTowerEquiv hML hLK).symm
      (q, QuotientGroup.mk x) =
      QuotientGroup.mk (Quotient.out q * Subgroup.inclusion hLK x) := rfl
  rw [he]
  change A.ρ ((Quotient.out q).1 * x.1) a.1 =
    A.ρ (Quotient.out q).1 (A.ρ x.1 a.1)
  rw [map_mul]
  rfl

/-- The source proof of the source-private M026.018
`finiteTowerNormTransApplyAux`: transitivity of relative norms for closed
subgroups `M ≤ L ≤ K` with finite relative quotients. -/
private theorem finiteTowerNormTransApplyAux_aux
    (A : Rep ℤ G) (K L M : ClosedSubgroup G)
    (hML : M.toSubgroup ≤ L.toSubgroup)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)]
    [Finite (L.toSubgroup ⧸ M.toSubgroup.subgroupOf L.toSubgroup)]
    (a : ambientFixedAddSubgroup A M) :
    letI : Finite (K.toSubgroup ⧸ M.toSubgroup.subgroupOf K.toSubgroup) :=
      relativeTowerQuotientFinite K L M hML hLK
    relativeNorm A K L hLK (relativeNorm A L M hML a) =
      relativeNorm A K M (hML.trans hLK) a := by
  apply Subtype.ext
  let := Fintype.ofFinite (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)
  let := Fintype.ofFinite (L.toSubgroup ⧸ M.toSubgroup.subgroupOf L.toSubgroup)
  let totalFintype : Fintype
      (K.toSubgroup ⧸ M.toSubgroup.subgroupOf K.toSubgroup) :=
    Fintype.ofEquiv
      ((K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup) ×
        (L.toSubgroup ⧸ M.toSubgroup.subgroupOf L.toSubgroup))
      (Subgroup.quotientTowerEquiv hML hLK).symm
  have htotalFintype : Fintype.ofFinite
      (K.toSubgroup ⧸ M.toSubgroup.subgroupOf K.toSubgroup) = totalFintype :=
    Subsingleton.elim _ _
  have houter : ∀ q : K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup,
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
        rfl
      _ = A.ρ (Quotient.out q).1 (relativeNormValue A L M hML a) := rfl
  show relativeNormValue A K L hLK (relativeNorm A L M hML a) =
    relativeNormValue A K M (hML.trans hLK) a
  simp only [relativeNormValue]
  rw [htotalFintype]
  rw [Finset.sum_congr rfl (fun q _ ↦ houter q)]
  simp only [relativeNormValue]
  simp_rw [map_sum]
  rw [← Fintype.sum_prod_type (f := fun p :
    (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup) ×
      (L.toSubgroup ⧸ M.toSubgroup.subgroupOf L.toSubgroup) ↦
        A.ρ (Quotient.out p.1).1
          (relativeCosetAction A L M hML a p.2))]
  calc
    ∑ p : (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup) ×
        (L.toSubgroup ⧸ M.toSubgroup.subgroupOf L.toSubgroup),
        A.ρ (Quotient.out p.1).1 (relativeCosetAction A L M hML a p.2) =
      ∑ p, relativeCosetAction A K M (hML.trans hLK) a
        ((Subgroup.quotientTowerEquiv hML hLK).symm p) := by
          apply Fintype.sum_congr
          intro p
          exact (relativeCosetAction_towerProductEquiv_aux A K L M hML hLK a
            p.1 p.2).symm
    _ = ∑ q, relativeCosetAction A K M (hML.trans hLK) a q :=
      (Subgroup.quotientTowerEquiv hML hLK).symm.sum_comp
        (relativeCosetAction A K M (hML.trans hLK) a)


namespace ValuationData

variable {D : DegreeData G} {A : Rep ℤ G}

/-- The source proof of M025.023 `ValuationData.residueDegree_nsmul_dividedAt`
(not yet published): `f_K v_K = v ∘ N_{K|k}` before codomain restriction. -/
private theorem residueDegree_nsmul_dividedAt_aux (v : ValuationData D A)
    (K : FiniteAbstractField G)
    (a : ambientFixedAddSubgroup A K.field) :
    (K.residueDegree D : ℕ) • v.dividedAt K a = v.normCompositeAt K a :=
  zHatMulNat_zHatDivide (K.residueDegree D : ℕ)
    (K.residueDegree D).property
    (v.normCompositeAtInResidueImage K a)

/-- The source proof of M027.007 `ValuationData.normalizedValuation_tower`
(not yet published): for a finite tower `L | K`,
`v_K ∘ N_{L|K} = f_{L|K} v_L`. -/
private theorem normalizedValuation_tower_aux (v : ValuationData D A)
    (E : FiniteAbstractFieldExtension G)
    (a : ambientFixedAddSubgroup A E.field.field) :
    let ER := E.toFiniteResidueAbstractExtension D
    (ER.residueDegree : ℕ) •
        ((v.valuationAt E.field a : v.valueGroup) : ZHat) =
      ((v.valuationAt E.base
        (relativeNorm A E.base.field E.field.field E.below a) :
          v.valueGroup) : ZHat) := by
  let ER := E.toFiniteResidueAbstractExtension D
  apply zHatMulNat_injective (E.base.residueDegree D).property
  change (ER.base.residueDegree : ℕ) •
      ((ER.residueDegree : ℕ) • v.dividedAt E.field a) =
    (ER.base.residueDegree : ℕ) •
      v.dividedAt E.base
        (relativeNorm A E.base.field E.field.field E.below a)
  rw [smul_smul, Nat.mul_comm (ER.base.residueDegree : ℕ),
    DegreeData.residueDegree_mul_absoluteResidueDegree_aux D ER]
  change (E.field.residueDegree D : ℕ) • v.dividedAt E.field a =
    (E.base.residueDegree D : ℕ) •
      v.dividedAt E.base
        (relativeNorm A E.base.field E.field.field E.below a)
  rw [residueDegree_nsmul_dividedAt_aux v E.field,
    residueDegree_nsmul_dividedAt_aux v E.base]
  change v.toAddMonoidHom (normToBase A E.field.field a) =
    v.toAddMonoidHom
      (normToBase A E.base.field
        (relativeNorm A E.base.field E.field.field E.below a))
  let T : DegreeData.FiniteTower G := {
    top := E.field.field
    middle := E.base.field
    base := baseField G
    top_le_middle := E.below
    middle_le_base := le_baseField E.base.field
    finiteTopQuotient := E.finiteQuotient
    finiteBaseQuotient := E.base.finite }
  exact congrArg v.toAddMonoidHom
    (by simpa [T, normToBase] using
      (finiteTowerNormTransApplyAux_aux A T.base T.middle T.top
        T.top_le_middle T.middle_le_base a).symm)


end ValuationData

/-- In a finite totally ramified extension, the normalized valuation of an
element from the lower field is multiplied by the extension degree after
inclusion into the upper field.  This is the valuation identity used for
`M/M⁰`. -/
theorem abstractReciprocity_valuationAt_fixedFieldInclusion_of_totallyRamified
    {D : DegreeData G} {A : Rep ℤ G} (v : ValuationData D A)
    (E : FiniteAbstractFieldExtension G)
    (hTot : E.IsTotallyRamified D)
    (x : ambientFixedAddSubgroup A E.base.field) :
    abstractReciprocity_valuationAt_fixedFieldInclusion_of_totallyRamifiedStatement
      v E hTot x := by
  show ((v.valuationAt E.field
      (fixedFieldInclusion A E.base.field E.field.field E.below x) :
      v.valueGroup) : ZHat) =
      (E.degree : ℕ) •
        ((v.valuationAt E.base x : v.valueGroup) : ZHat)
  let EF := E.toFiniteAbstractExtension
  let hEFfinite : Finite
      (E.base.field.toSubgroup ⧸
        extensionSubgroup E.base.field E.field.field E.below) :=
    EF.finiteQuotient
  have htower := ValuationData.normalizedValuation_tower_aux v E
    (fixedFieldInclusion A E.base.field E.field.field E.below x)
  have hresidue : (E.residueDegree D : ℕ) = 1 :=
    DegreeData.FiniteAbstractExtension.residueDegree_eq_one_of_isTotallyRamified_aux
      EF D hTot
  change (E.residueDegree D : ℕ) •
      ((v.valuationAt E.field
        (fixedFieldInclusion A E.base.field E.field.field E.below x) :
          v.valueGroup) : ZHat) =
    ((v.valuationAt E.base
      (relativeNorm A E.base.field E.field.field E.below
        (fixedFieldInclusion A E.base.field E.field.field E.below x)) :
          v.valueGroup) : ZHat) at htower
  rw [hresidue, one_nsmul] at htower
  have hbelow : E.below = EF.below := Subsingleton.elim _ _
  rw [hbelow] at htower
  change
    ((v.valuationAt E.field
      (fixedFieldInclusion A EF.base EF.field EF.below x) :
        v.valueGroup) : ZHat) =
      ((v.valuationAt E.base
        (relativeNorm A EF.base EF.field EF.below
          (fixedFieldInclusion A EF.base EF.field EF.below x)) :
            v.valueGroup) : ZHat) at htower
  rw [relativeNorm_fixedFieldInclusion_aux A EF x] at htower
  have hfixedFieldInclusion :
      fixedFieldInclusion A EF.base EF.field EF.below x =
        fixedFieldInclusion A E.base.field E.field.field E.below x := by
    apply Subtype.ext
    rfl
  rw [hfixedFieldInclusion] at htower
  have htower' :
      ((v.valuationAt E.field
        (fixedFieldInclusion A E.base.field E.field.field E.below x) :
          v.valueGroup) : ZHat) =
        ((v.valuationAt E.base ((E.degree : ℕ) • x) :
          v.valueGroup) : ZHat) := by
    simpa [EF, FiniteAbstractFieldExtension.degree] using htower
  calc
    ((v.valuationAt E.field
      (fixedFieldInclusion A E.base.field E.field.field E.below x) :
        v.valueGroup) : ZHat) =
        ((v.valuationAt E.base ((E.degree : ℕ) • x) :
          v.valueGroup) : ZHat) := htower'
    _ = (E.degree : ℕ) •
        ((v.valuationAt E.base x : v.valueGroup) : ZHat) :=
      congrArg Subtype.val
        (map_nsmul (v.valuationAt E.base) (E.degree : ℕ) x)

end Langlands.NYLL.ClassFormation
