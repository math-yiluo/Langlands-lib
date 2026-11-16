/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 746, 16 November 2026 UTC:
Extract only the proof of M083.003
`ValuationData.valuationAt_extensionFixedRepresentation_action` from
Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/TotallyRamified.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix, state the theorem as the published Statement applied to
the source parameters, and import the published statement module together
with the published modules and proofs listed in the paired Markdown. The
source proof cites the unpublished M032.018
`ValuationData.valuationAt_normalExtensionAction`; it is replaced by a
private theorem with the source proof of M032.018, which in turn uses the
unpublished M025.023 `ValuationData.residueDegree_nsmul_dividedAt`, M026.013
`relativeNorm_normalExtensionAction` and M026.019
`DegreeData.FiniteTower.norm_trans_apply` (with the source-private M026.017
and M026.018). These are reproduced as private `_aux` theorems from their
source proofs, in the form of Worker 5264's unreviewed shared draft
(revision 1) of Task 7030: `extensionSubgroup K L hLK` is written as its
abbreviation body, the `rfl` lemmas M024.002, M024.010 and M026.012 are
replaced by `change`, `show` and `rfl` steps, and M026.018 is applied
directly instead of M026.019. The original LICENSE and NOTICE are retained
in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.TotallyRamified.ActionValuation.Statements
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteTower.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.U014.Proofs
import Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.U005.Proofs
import Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.Divide.U017.Proofs

/-!
# Normalized valuation is invariant under the quotient action

The exact proof of M083.003: for a finite normal abstract extension `L | K`,
the normalized valuation `v_L` is invariant under the action of
`G_K / G_L` on the fixed coefficient representation `A_L`.
-/

namespace Langlands.NYLL.ClassFormation

open KummerTheory

open CyclicCohomology

open scoped BigOperators

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/-- The source proof of M026.013 `relativeNorm_normalExtensionAction` (not yet
published): for a finite normal extension, the relative norm is invariant
under the `G_K`-conjugacy action on `A_L`. -/
private theorem relativeNorm_normalExtensionAction_aux
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal)
    [Finite (K.toSubgroup ⧸ (L.toSubgroup.subgroupOf K.toSubgroup))]
    (k : K.toSubgroup) (a : ambientFixedAddSubgroup A L) :
    relativeNorm A K L hLK (normalExtensionAction A K L hLK hnormal k a) =
      relativeNorm A K L hLK a := by
  apply Subtype.ext
  let := Fintype.ofFinite (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)
  let e : (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup) ≃
      (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup) :=
    Equiv.mulRight (QuotientGroup.mk k)
  have hterm : ∀ q : K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup,
      relativeCosetAction A K L hLK (normalExtensionAction A K L hLK hnormal k a) q =
        relativeCosetAction A K L hLK a (e q) := by
    intro q
    refine Quotient.inductionOn' q ?_
    intro x
    have he : e (QuotientGroup.mk x) = QuotientGroup.mk (x * k) := rfl
    rw [he]
    change A.ρ x.1 (A.ρ k.1 a.1) = A.ρ (x.1 * k.1) a.1
    rw [map_mul]
    rfl
  change relativeNormValue A K L hLK (normalExtensionAction A K L hLK hnormal k a) =
    relativeNormValue A K L hLK a
  simp only [relativeNormValue]
  simp_rw [hterm]
  exact e.sum_comp (relativeCosetAction A K L hLK a)

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

/-- Local copy of the source proof of M032.018
`ValuationData.valuationAt_normalExtensionAction` (not yet published):
normalized valuation is invariant under the Galois action in a finite
tower. -/
private theorem valuationAt_normalExtensionAction_aux
    (v : ValuationData D A) (E : FiniteAbstractFieldExtension G)
    (hnormal : (extensionSubgroup E.base.field E.field.field E.below).Normal)
    (k : E.base.field.toSubgroup)
    (a : ambientFixedAddSubgroup A E.field.field) :
    v.valuationAt E.field
        (normalExtensionAction A E.base.field E.field.field E.below
          hnormal k a) =
      v.valuationAt E.field a := by
  apply Subtype.ext
  apply zHatMulNat_injective (E.field.residueDegree D).property
  change (E.field.residueDegree D : ℕ) •
      ((v.valuationAt E.field
        (normalExtensionAction A E.base.field E.field.field E.below
          hnormal k a) : v.valueGroup) : ZHat) =
    (E.field.residueDegree D : ℕ) •
      ((v.valuationAt E.field a : v.valueGroup) : ZHat)
  calc
    (E.field.residueDegree D : ℕ) •
        ((v.valuationAt E.field
          (normalExtensionAction A E.base.field E.field.field E.below
            hnormal k a) : v.valueGroup) : ZHat) =
      v.normCompositeAt E.field
        (normalExtensionAction A E.base.field E.field.field E.below
          hnormal k a) :=
        residueDegree_nsmul_dividedAt_aux v E.field _
    _ = v.normCompositeAt E.field a := by
      change v.toAddMonoidHom
          (normToBase A E.field.field
            (normalExtensionAction A E.base.field E.field.field E.below
              hnormal k a)) =
        v.toAddMonoidHom (normToBase A E.field.field a)
      congr 1
      let T : DegreeData.FiniteTower G := {
        top := E.field.field
        middle := E.base.field
        base := baseField G
        top_le_middle := E.below
        middle_le_base := le_baseField E.base.field
        finiteTopQuotient := E.finiteQuotient
        finiteBaseQuotient := E.base.finite }
      have hN : relativeNorm A E.base.field E.field.field E.below
            (normalExtensionAction A E.base.field E.field.field E.below
              hnormal k a) =
          relativeNorm A E.base.field E.field.field E.below a :=
        relativeNorm_normalExtensionAction_aux A E.base.field E.field.field
          E.below hnormal k a
      calc
        relativeNorm A (baseField G) E.field.field
            (E.below.trans (le_baseField E.base.field))
            (normalExtensionAction A E.base.field E.field.field E.below
              hnormal k a) =
          relativeNorm A (baseField G) E.base.field
            (le_baseField E.base.field)
            (relativeNorm A E.base.field E.field.field E.below
              (normalExtensionAction A E.base.field E.field.field E.below
                hnormal k a)) :=
          (finiteTowerNormTransApplyAux_aux A T.base T.middle T.top
            T.top_le_middle T.middle_le_base _).symm
        _ = relativeNorm A (baseField G) E.base.field
            (le_baseField E.base.field)
            (relativeNorm A E.base.field E.field.field E.below a) := by
          rw [hN]
        _ = relativeNorm A (baseField G) E.field.field
            (E.below.trans (le_baseField E.base.field)) a :=
          finiteTowerNormTransApplyAux_aux A T.base T.middle T.top
            T.top_le_middle T.middle_le_base a
    _ = (E.field.residueDegree D : ℕ) •
        ((v.valuationAt E.field a : v.valueGroup) : ZHat) :=
      (residueDegree_nsmul_dividedAt_aux v E.field a).symm

/-- Normalized valuation is invariant under the actual quotient action.
This is the quotient-representation form of the unit-cohomology axiom's
`valuationAt_normalExtensionAction`. -/
theorem valuationAt_extensionFixedRepresentation_action
    (v : ValuationData D A)
    (E : FiniteAbstractFieldExtension G)
    (hnormal : (extensionSubgroup
      E.base.field E.field.field E.below).Normal)
    (q : E.base.field.toSubgroup ⧸
      extensionSubgroup E.base.field E.field.field E.below)
    (a : (extensionFixedRepresentation A E.base.field E.field.field
      E.below hnormal).V) :
    valuationAt_extensionFixedRepresentation_actionStatement v E hnormal q a := by
  show v.valuationAt E.field
      (extensionFixedRepresentationEquiv A E.base.field E.field.field
        E.below hnormal
        ((extensionFixedRepresentation A E.base.field E.field.field
          E.below hnormal).ρ q a)) =
    v.valuationAt E.field
      (extensionFixedRepresentationEquiv A E.base.field E.field.field
        E.below hnormal a)
  let := hnormal
  refine Quotient.inductionOn' q ?_
  intro r
  let aL : ambientFixedAddSubgroup A E.field.field :=
    extensionFixedRepresentationEquiv A E.base.field E.field.field
      E.below hnormal a
  have heq :
      extensionFixedRepresentationEquiv A E.base.field E.field.field
          E.below hnormal
          ((extensionFixedRepresentation A E.base.field E.field.field
            E.below hnormal).ρ
            (QuotientGroup.mk r) a) =
        normalExtensionAction A E.base.field E.field.field E.below
          hnormal r aL := by
    apply Subtype.ext
    rfl
  rw [heq]
  exact valuationAt_normalExtensionAction_aux v E hnormal r aL

end ValuationData

end Langlands.NYLL.ClassFormation
