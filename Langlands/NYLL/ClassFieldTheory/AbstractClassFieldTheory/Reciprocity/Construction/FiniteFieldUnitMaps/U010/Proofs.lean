/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FiniteFieldUnitMaps.Statements
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.ValuationLaws.Tower.Statements
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteTower.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.U005.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.AbstractExtension.U036.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteResidue.U027.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.U014.Proofs
import Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.U005.Proofs
import Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.Divide.U017.Proofs

/-!
# NYLL M045.010: the relative norm of a unit is a unit

Modified by Worker 745, 16 November 2026: prove the published target
`ValuationData.relativeNorm_mem_unitAddSubgroupStatement` (M045.010) by the
source proof of `ValuationData.relativeNorm_mem_unitAddSubgroup` in
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FiniteFieldUnitMaps.lean`
at fbd320cd8b1b06487c58227e92eb135794267709. Prefix the namespace with
`Langlands.NYLL`, give the theorem the published proposition as its type, and
replace the source imports by the published statement modules and the
published modules and proofs listed in the paired Markdown. The source proof
uses two results whose proofs are not yet published: M028.009
`ValuationData.mem_unitAddSubgroup_iff` and M027.007
`ValuationData.normalizedValuation_tower`. Their source proofs are reproduced
here as private theorems with an `_aux` suffix, the latter (with its own
unpublished prerequisites M010.103, M011.017, M025.023 and the source-private
M026.017 and M026.018) following the shared draft of Worker 5264 for Task
dd6e7eae-0db1-4832-bb64-e830afecdaf5, where `extensionSubgroup K L hLK` is
written as its abbreviation body `L.toSubgroup.subgroupOf K.toSubgroup` and
rewrites with the `rfl` lemmas M024.002 `relativeCosetAction_mk` and M024.010
`relativeNorm_apply_coe` are replaced by `change`, `show` and `rfl` steps. See
the paired Markdown and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

open KummerTheory

open CyclicCohomology

open scoped BigOperators

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- The source proof of M010.103
`FiniteAbstractExtension.relativeResidueDegreeCardinal_eq_coe` (not yet
published): for a finite extension, the cardinal-valued relative residue
degree is the cardinal cast of the positive natural residue degree. -/
private theorem relativeResidueDegreeCardinal_eq_coe_aux
    (E : FiniteAbstractExtension G) (D : DegreeData G) :
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
  rw [relativeResidueDegreeCardinal_eq_coe_aux E.toFiniteAbstractExtension D] at h
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

/-- The source proof of M028.009 `ValuationData.mem_unitAddSubgroup_iff`
(not yet published): `u ∈ v.unitAddSubgroup K` exactly when
`v.valuationAt K u = 0`. -/
private theorem mem_unitAddSubgroup_iff_aux (v : ValuationData D A)
    (K : FiniteAbstractField G)
    (u : ambientFixedAddSubgroup A K.field) :
    u ∈ v.unitAddSubgroup K ↔ v.valuationAt K u = 0 :=
  Iff.rfl

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
(not yet published), the norm--valuation formula: for a finite tower
`L | K`, `v_K ∘ N_{L|K} = f_{L|K} v_L`. -/
private theorem normalizedValuation_tower_aux (v : ValuationData D A)
    (E : FiniteAbstractFieldExtension G)
    (a : ambientFixedAddSubgroup A E.field.field) :
    let ER := E.toFiniteResidueAbstractExtension D
    (ER.residueDegree : ℕ) •
        ((v.valuationAt E.field a : v.valueGroup) : ZHat) =
      ((v.valuationAt E.base
        (relativeNorm A E.base.field E.field.field E.below a) : v.valueGroup) : ZHat) := by
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

/-- The norm of a unit through an arbitrary finite extension is a unit.
This is the valuation-theoretic step used when a finite Galois refinement
is pushed back down to the originally prescribed intermediate field. -/
theorem relativeNorm_mem_unitAddSubgroup
    (v : ValuationData D A) (E : FiniteAbstractFieldExtension G)
    (u : v.unitAddSubgroup E.field) :
    relativeNorm_mem_unitAddSubgroupStatement v E u := by
  show relativeNorm A E.base.field E.field.field E.below u.1 ∈
    v.unitAddSubgroup E.base
  rw [mem_unitAddSubgroup_iff_aux]
  apply Subtype.ext
  have h := normalizedValuation_tower_aux v E u.1
  let ER := E.toFiniteResidueAbstractExtension D
  change (ER.residueDegree : ℕ) •
      ((v.valuationAt E.field u.1 : v.valueGroup) : ZHat) =
    ((v.valuationAt E.base
      (relativeNorm A E.base.field E.field.field E.below u.1) :
        v.valueGroup) : ZHat) at h
  have hu : v.valuationAt E.field u.1 = 0 := u.2
  simpa [hu] using h.symm

end ValuationData

end Langlands.NYLL.ClassFormation
