/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.UnramifiedNormQuotient.PrimeClass.Statements
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FiniteNormQuotient.U010.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FiniteNormQuotient.U012.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.PrimeElements.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.ValuationLaws.Tower.Statements
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteTower.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteAbstractField.Extension.NumericDefinitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.U005.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.AbstractExtension.U036.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteResidue.U027.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.U014.Proofs
import Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.U005.Proofs
import Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.Divide.U017.Proofs

/-!
# NYLL M058.014: the additive order of a prime class

Modified by Worker 745, 16 November 2026: prove the published target
`ValuationData.primeClass_addOrderOfStatement` (M058.014) by the source proof
of `ValuationData.primeClass_addOrderOf` in
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/UnramifiedNormQuotient.lean`
at fbd320cd8b1b06487c58227e92eb135794267709. Prefix the namespace with
`Langlands.NYLL`, give the theorem the published proposition as its type, and
replace the source imports by the published statement modules and the
published modules and proofs listed in the paired Markdown. The source proof
uses results whose proofs are not yet published; they are proved here as
private theorems with an `_aux` suffix. M039.010 `finiteNormClass_nsmul`,
M039.012 `finiteNormClass_eq_zero_iff`, M028.006
`ValuationData.oneValue_coe`, M028.003 `relativeNorm_fixedFieldInclusion` and
M027.007 `ValuationData.normalizedValuation_tower` (with its own unpublished
prerequisites M010.103, M011.017, M025.023 and the source-private M026.017 and
M026.018) follow their source proofs, the last two with the Lean text of the
shared drafts of Worker 5264 for Task dd6e7eae-0db1-4832-bb64-e830afecdaf5
and Task 905dd316-beba-4d50-8384-657eb2f1e35f, where
`extensionSubgroup K L hLK` is written as its abbreviation body
`L.toSubgroup.subgroupOf K.toSubgroup`, rewrites with the `rfl` lemmas
M024.002 `relativeCosetAction_mk`, M024.010 `relativeNorm_apply_coe` and
M028.002 `fixedFieldInclusion_coe` are replaced by `change`, `show` and `rfl`
steps, and M010.092 `extensionSubgroup_index_eq_degree` is replaced by a local
fact proved by its source proof. M010.138
`FiniteAbstractFieldExtension.residueDegree_eq_degree_of_isUnramified` (with
M010.100) is proved by a shorter route than the source fundamental identity;
see the paired Markdown and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

/-! Integrator, 16 November 2026: reuse the independently accepted public
M039.010 and M039.012 proofs and remove the corresponding private copies.
The preceding dated port account describes the original submission. -/

namespace Langlands.NYLL.ClassFormation

open KummerTheory

open CyclicCohomology

open scoped BigOperators

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/-- Replaces M010.138
`FiniteAbstractFieldExtension.residueDegree_eq_degree_of_isUnramified` and
M010.100 `FiniteAbstractExtension.residueDegree_eq_degree_of_isUnramified`
(not yet published): in an unramified finite field extension the positive
residue degree is the positive degree.  Both are relative indices; the residue
degree is the index of `L ⊔ ker d` in `K`, and unramifiedness
`K ⊓ ker d ≤ L` makes the saturated subgroup `(L ⊔ ker d) ⊓ K` equal to `L`. -/
private theorem residueDegree_eq_degree_of_isUnramified_aux
    (E : FiniteAbstractFieldExtension G) (D : DegreeData G)
    (hE : E.IsUnramified D) :
    (E.residueDegree D : ℕ) = (E.degree : ℕ) := by
  have hLK : E.field.field.toSubgroup ≤ E.base.field.toSubgroup := E.below
  have hUn : E.base.field.toSubgroup ⊓ D.degree.toMonoidHom.ker ≤
      E.field.field.toSubgroup := hE
  have hsat : (E.field.field.toSubgroup ⊔ D.degree.toMonoidHom.ker) ⊓
      E.base.field.toSubgroup = E.field.field.toSubgroup := by
    apply le_antisymm
    · rintro x ⟨hxSup, hxK⟩
      obtain ⟨y, hyL, z, hzKer, rfl⟩ :=
        (Subgroup.mem_sup_of_normal_right).mp hxSup
      have hzK : z ∈ E.base.field.toSubgroup := by
        have hz : z = y⁻¹ * (y * z) := by group
        rw [hz]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hLK hyL)) hxK
      exact Subgroup.mul_mem _ hyL (hUn ⟨hzK, hzKer⟩)
    · intro x hx
      exact ⟨Subgroup.mem_sup_left hx, hLK hx⟩
  have hres : (E.residueDegree D : ℕ) =
      (E.field.field.toSubgroup.map D.degree.toMonoidHom).relIndex
        (E.base.field.toSubgroup.map D.degree.toMonoidHom) := rfl
  have hdeg : (E.degree : ℕ) =
      E.field.field.toSubgroup.relIndex E.base.field.toSubgroup := rfl
  rw [hres, hdeg, ← Subgroup.relIndex_comap, Subgroup.comap_map_eq,
    ← Subgroup.inf_relIndex_right, hsat]

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

/-- The source proof of M028.003 `relativeNorm_fixedFieldInclusion` (not yet
published): the norm of an element already fixed over `K` is its `[L:K]`-fold
sum. -/
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

namespace ValuationData

variable {D : DegreeData G} {A : Rep ℤ G}

/-- The source proof of M028.006 `ValuationData.oneValue_coe` (not yet
published): the value one coerces to `(1 : ZHat)`. -/
private theorem oneValue_coe_aux (v : ValuationData D A) :
    (v.oneValue : ZHat) = 1 :=
  rfl

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

/-- A prime class has exact additive order `[L : K]` in an unramified
norm quotient.  The lower bound is read after reduction in `ℤ̂/nℤ̂`; the
upper bound is the norm of the included prime. -/
theorem primeClass_addOrderOf
    (v : ValuationData D A)
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (hUnramified :
      (DegreeData.AbstractExtension.mk L K.field hLK).IsUnramified D)
    (π : ambientFixedAddSubgroup A K.field) (hπ : v.IsPrimeElement K π) :
    primeClass_addOrderOfStatement v K L hLK hUnramified π hπ := by
  show addOrderOf
      (finiteNormClass A K.field L hLK π) =
      ((FiniteAbstractFieldExtension.ofInclusion L K hLK).degree : ℕ)
  let E := FiniteAbstractFieldExtension.ofInclusion L K hLK
  let n := (E.degree : ℕ)
  have hUn : E.IsUnramified D := by
    change (DegreeData.AbstractExtension.mk L K.field hLK).IsUnramified D
    exact hUnramified
  let g : FiniteNormQuotient A K.field L hLK :=
    finiteNormClass A K.field L hLK π
  have hn : 0 < n := E.degree.property
  have hng : n • g = 0 := by
    change n • finiteNormClass A K.field L hLK π = 0
    rw [← finiteNormClass_nsmul]
    apply (finiteNormClass_eq_zero_iff A K.field L hLK _).2
    refine ⟨fixedFieldInclusion A K.field L hLK π, ?_⟩
    have hnorm :=
      relativeNorm_fixedFieldInclusion_aux A E.toFiniteAbstractExtension π
    change relativeNorm A K.field L hLK
        (fixedFieldInclusion A K.field L hLK π) = n • π at hnorm
    exact hnorm
  have hdiv : ∀ m : ℕ, m • g = 0 → n ∣ m := by
    intro m hm
    have hm' :
        finiteNormClass A K.field L hLK (m • π) = 0 := by
      rw [finiteNormClass_nsmul A K.field L hLK m π]
      exact hm
    have hmNorm := (finiteNormClass_eq_zero_iff A K.field L hLK _).1 hm'
    obtain ⟨b, hb⟩ := hmNorm
    have htower := normalizedValuation_tower_aux v E b
    change (E.residueDegree D : ℕ) • _ = _ at htower
    rw [residueDegree_eq_degree_of_isUnramified_aux E D hUn] at htower
    have hval :
        n • ((v.valuationAt E.field b : v.valueGroup) : ZHat) =
          m • (1 : ZHat) := by
      calc
        n • ((v.valuationAt E.field b : v.valueGroup) : ZHat) =
            ((v.valuationAt K (relativeNorm A K.field L hLK b) :
              v.valueGroup) : ZHat) := htower
        _ = ((v.valuationAt K (m • π) : v.valueGroup) : ZHat) := by
          rw [hb]
        _ = m • ((v.valuationAt K π : v.valueGroup) : ZHat) := by
          exact congrArg Subtype.val (map_nsmul (v.valuationAt K) m π)
        _ = m • (1 : ZHat) := by rw [hπ, oneValue_coe_aux]
    have hred := congrArg (fun z : ZHat => zHatReduction n hn z) hval
    have hredOne : zHatReduction n hn (1 : ZHat) = 1 := rfl
    have hred' :
        n • zHatReduction n hn
            ((v.valuationAt E.field b : v.valueGroup) : ZHat) =
          m • (1 : ZMod n) := by
      simpa only [map_nsmul, hredOne] using hred
    have hmzero : (m : ZMod n) = 0 := by
      have hmzero' : m • (1 : ZMod n) = 0 := by
        rw [← hred']
        simp [nsmul_eq_mul]
      simpa using hmzero'
    exact (ZMod.natCast_eq_zero_iff m n).1 hmzero
  apply Nat.dvd_antisymm
  · exact (addOrderOf_dvd_iff_nsmul_eq_zero).2 hng
  · exact hdiv (addOrderOf g) (addOrderOf_nsmul_eq_zero g)

end ValuationData

end Langlands.NYLL.ClassFormation
