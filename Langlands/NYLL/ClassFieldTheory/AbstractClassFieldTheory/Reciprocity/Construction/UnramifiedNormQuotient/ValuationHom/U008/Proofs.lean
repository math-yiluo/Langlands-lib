/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 746, 16 November 2026 UTC:
Extract only the proof of the private source theorem M058.008
`ValuationData.finiteNormSubgroup_le_unramifiedValuationHom_ker` from
Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/UnramifiedNormQuotient.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Name it
`Langlands.NYLL.PortInternal.M058.d008`, state it as the published
Statement `d008Statement` applied to the source parameters, and import the
published statement module together with the published modules and proofs
listed in the paired Markdown. The source-private helper M058.006
`ValuationData.valueModulo_eq_zero_iff` is reproduced by its source proof
as a private theorem. The source proof cites the unpublished M010.138
`FiniteAbstractFieldExtension.residueDegree_eq_degree_of_isUnramified` and
M027.007 `ValuationData.normalizedValuation_tower`; they are replaced by
private theorems with their source proofs, together with the unpublished
source chain behind them (M010.100, M010.096, M010.095 and M006.009 with
M006.008 and M006.007; M011.017 with M010.103, M025.023 and M026.019 with
the source-private M026.017 and M026.018). These private theorems are taken
from Worker 5264's unreviewed shared draft (revision 1) of Task 7030:
`extensionSubgroup K L hLK` is written as its abbreviation body, the `rfl`
lemmas M010.091, M010.093, M010.094, M024.002 and M024.010 are replaced by
`change`, `show` and `rfl` steps, and M026.018 is applied directly instead
of M026.019. The original LICENSE and NOTICE are retained in
licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.UnramifiedNormQuotient.ValuationHom.Statements
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteTower.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteAbstractField.Extension.NumericDefinitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteResidueExtension.ResidueDegreeDefinitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Indices.U006.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.U005.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.AbstractExtension.U036.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteResidue.U027.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.U014.Proofs
import Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.U005.Proofs
import Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.Divide.U017.Proofs

/-!
# Finite norms lie in the kernel of the unramified valuation map

The exact proof of the private source theorem M058.008: for an unramified
finite extension `L | K`, every norm from `A_L` lies in the kernel of the
normalized valuation of `A_K` reduced modulo `[L : K]`.
-/

namespace Langlands.NYLL.ClassFormation

open KummerTheory

open CyclicCohomology

open scoped BigOperators

/-- The source proof of M006.009 `relIndex_eq_map_relIndex_mul_inf_ker_relIndex`
(not yet published), with the source proofs of M006.008
`map_relIndex_eq_saturation_relIndex` and M006.007
`relIndex_saturation_eq_inf_ker_relIndex` as the local facts `hmap` and
`hsat`. -/
private theorem relIndex_eq_map_relIndex_mul_inf_ker_relIndex_aux
    {H Q : Type*} [Group H] [Group Q] (d : H →* Q) {L K : Subgroup H}
    (hLK : L ≤ K) :
    L.relIndex K =
      (L.map d).relIndex (K.map d) * (L ⊓ d.ker).relIndex (K ⊓ d.ker) := by
  have hmap : (L.map d).relIndex (K.map d) = (K ⊓ (L ⊔ d.ker)).relIndex K := by
    rw [← Subgroup.relIndex_comap, Subgroup.comap_map_eq, ← Subgroup.inf_relIndex_right,
      inf_comm]
  have hsat : L.relIndex (K ⊓ (L ⊔ d.ker)) = (L ⊓ d.ker).relIndex (K ⊓ d.ker) := by
    unfold Subgroup.relIndex
    exact Nat.card_congr (kernelCosetEquivSaturation d hLK).symm
  rw [hmap, ← hsat, mul_comm]
  exact (Subgroup.relIndex_mul_relIndex L (K ⊓ (L ⊔ d.ker)) K
    (fun x hx ↦ ⟨hLK hx, (show L ≤ L ⊔ d.ker from le_sup_left) hx⟩) inf_le_left).symm

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace DegreeData

namespace FiniteAbstractExtension

variable (E : FiniteAbstractExtension G)

/-- The source proof of M010.095
`FiniteAbstractExtension.degree_eq_residueDegree_mul_ramificationIndex` (not
yet published), with the `rfl` lemmas M010.091 `relIndex_eq_degree`, M010.093
`mapped_relIndex_eq_residueDegree` and M010.094
`inertia_relIndex_eq_ramificationIndex` replaced by `change`. -/
private theorem degree_eq_residueDegree_mul_ramificationIndex_aux
    (D : DegreeData G) :
    (E.degree : ℕ) =
      (E.residueDegree D : ℕ) * (E.ramificationIndex D : ℕ) := by
  change E.field.toSubgroup.relIndex E.base.toSubgroup =
    (E.field.toSubgroup.map D.degree.toMonoidHom).relIndex
        (E.base.toSubgroup.map D.degree.toMonoidHom) *
      (E.field.toSubgroup ⊓ D.degree.toMonoidHom.ker).relIndex
        (E.base.toSubgroup ⊓ D.degree.toMonoidHom.ker)
  exact relIndex_eq_map_relIndex_mul_inf_ker_relIndex_aux
    D.degree.toMonoidHom E.below

/-- The source proof of M010.096
`FiniteAbstractExtension.ramificationIndex_eq_one_of_isUnramified` (not yet
published), with the `rfl` lemma M010.094 replaced by `change`. -/
private theorem ramificationIndex_eq_one_of_isUnramified_aux (D : DegreeData G)
    (hE : E.IsUnramified D) :
    (E.ramificationIndex D : ℕ) = 1 := by
  change (E.field.toSubgroup ⊓ D.degree.toMonoidHom.ker).relIndex
      (E.base.toSubgroup ⊓ D.degree.toMonoidHom.ker) = 1
  rw [Subgroup.relIndex_eq_one]
  intro x hx
  exact ⟨hE hx, hx.2⟩

/-- The source proof of M010.100
`FiniteAbstractExtension.residueDegree_eq_degree_of_isUnramified` (not yet
published). -/
private theorem residueDegree_eq_degree_of_isUnramified_aux (D : DegreeData G)
    (hE : E.IsUnramified D) :
    (E.residueDegree D : ℕ) = (E.degree : ℕ) := by
  rw [degree_eq_residueDegree_mul_ramificationIndex_aux E D,
    ramificationIndex_eq_one_of_isUnramified_aux E D hE, mul_one]

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

/-- The source proof of M010.138
`FiniteAbstractFieldExtension.residueDegree_eq_degree_of_isUnramified` (not
yet published): in an unramified finite field extension, the positive
relative residue degree is the positive extension degree. -/
private theorem FiniteAbstractFieldExtension.residueDegree_eq_degree_of_isUnramified_aux
    (E : FiniteAbstractFieldExtension G) (D : DegreeData G)
    (hE : E.IsUnramified D) :
    (E.residueDegree D : ℕ) = (E.degree : ℕ) :=
  DegreeData.FiniteAbstractExtension.residueDegree_eq_degree_of_isUnramified_aux
    E.toFiniteAbstractExtension D hE

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

/-- The source proof of the source-private M058.006
`ValuationData.valueModulo_eq_zero_iff`: a value reduces to zero modulo `n`
exactly when it is an `n`-fold multiple in the value group. -/
private theorem valueModulo_eq_zero_iff_aux
    (v : ValuationData D A) (n : ℕ) (hn : 0 < n)
    (z : v.valueGroup) :
    v.valueModulo n hn z = 0 ↔ ∃ w : v.valueGroup, z = n • w := by
  constructor
  · intro hz
    have hq :
        (QuotientAddGroup.mk' (nsmulWithin v.valueGroup n)) z = 0 := by
      apply (v.cyclic_value_quotients n hn).injective
      change v.valueModulo n hn z = v.valueModulo n hn 0
      rw [hz, map_zero]
    obtain ⟨w, hw⟩ :=
      (QuotientAddGroup.eq_zero_iff z).1 hq
    exact ⟨w, hw.symm⟩
  · rintro ⟨w, rfl⟩
    have hq :
        (QuotientAddGroup.mk' (nsmulWithin v.valueGroup n)) (n • w) = 0 := by
      apply (QuotientAddGroup.eq_zero_iff _).2
      exact ⟨w, rfl⟩
    change (v.cyclic_value_quotients n hn)
        ((QuotientAddGroup.mk' (nsmulWithin v.valueGroup n)) (n • w)) = 0
    rw [hq, map_zero]

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

end Langlands.NYLL.ClassFormation

namespace Langlands.NYLL.PortInternal.M058

open ClassFormation

open KummerTheory

open CyclicCohomology

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
variable {D : DegreeData G} {A : Rep ℤ G}

/-- For an unramified finite extension `L | K`, every norm from `A_L` lies in
the kernel of the normalized valuation of `A_K` reduced modulo `[L : K]`
(source: the private
`ValuationData.finiteNormSubgroup_le_unramifiedValuationHom_ker`). -/
theorem d008
    (v : ValuationData D A)
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (hUnramified :
      (DegreeData.AbstractExtension.mk L K.field hLK).IsUnramified D) :
    d008Statement v K L hLK hUnramified := by
  show finiteNormSubgroup A K.field L hLK ≤ (d007 v K L hLK).ker
  rintro _ ⟨a, rfl⟩
  let E := FiniteAbstractFieldExtension.ofInclusion L K hLK
  let n := (E.degree : ℕ)
  have hUn : E.IsUnramified D := by
    change (DegreeData.AbstractExtension.mk L K.field hLK).IsUnramified D
    exact hUnramified
  have htower := ValuationData.normalizedValuation_tower_aux v E a
  change (E.residueDegree D : ℕ) • _ = _ at htower
  rw [FiniteAbstractFieldExtension.residueDegree_eq_degree_of_isUnramified_aux
    E D hUn] at htower
  have hval : v.valuationAt K (relativeNorm A K.field L hLK a) =
      n • v.valuationAt E.field a := by
    apply Subtype.ext
    exact htower.symm
  change v.valueModulo n E.degree.property
      (v.valuationAt K (relativeNorm A K.field L hLK a)) = 0
  rw [hval]
  exact (ValuationData.valueModulo_eq_zero_iff_aux v n E.degree.property _).2
    ⟨v.valuationAt E.field a, rfl⟩

end Langlands.NYLL.PortInternal.M058
