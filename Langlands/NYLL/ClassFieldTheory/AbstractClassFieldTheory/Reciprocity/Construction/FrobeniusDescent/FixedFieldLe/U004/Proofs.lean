/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 754 (2026-11-16): extract the proof of M017.004
`frobeniusFixedField_le_of_restriction_eq_one` from
Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusDescent.lean
(lines 135–181) at commit fbd320cd8b1b06487c58227e92eb135794267709, together
with the source proof of M017.002 `extensionImageInInertiaQuotient_isClosed`
(lines 40–71 of the same file), whose proof was not yet published, as the
private lemma `extensionImageInInertiaQuotient_isClosed_aux`. Prefix the
namespace ClassFormation with Langlands.NYLL; import the published statement
module, the published M017.001 definition module and Mathlib's
`Mathlib.Topology.Algebra.OpenSubgroup`; state the theorem as its
`frobeniusFixedField_le_of_restriction_eq_oneStatement` applied to the source
binders, opening the proof with `show` of the unfolded conclusion; expand
`extensionSubgroup K.field L hLK` to its Mathlib body
`L.toSubgroup.subgroupOf K.field.toSubgroup` throughout, as in the statement.
The private lemma omits the source's unused first step, the local instance
`D.extensionInertiaWithin_isClosed K L hLK` (M014.022, then unpublished).
The unused `open CyclicCohomology` is omitted. The rest of both tactic proofs
is unchanged.
Retained license and notices: licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusDescent.FixedFieldLe.Statements
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusDescent.InertiaQuotientImage.Definitions
import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# A Frobenius lift with trivial restriction has fixed field containing `L` (NYLL M017.004)

If the restriction of a Frobenius lift `σ` to `G(L/K)` is trivial, then the
subgroup `G_Σ` of its fixed field lies in `G_L`.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- The image of `G_L` in `G_K / I_L` is closed.  This is the compact-image
step implicit in the Galois correspondence used.  (Local copy of the source
proof of M017.002, under a private name.) -/
private theorem extensionImageInInertiaQuotient_isClosed_aux
    (D : DegreeData G) [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup)] :
    IsClosed (D.extensionImageInInertiaQuotient K.field L hLK : Set
      (K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)) := by
  let E := L.toSubgroup.subgroupOf K.field.toSubgroup
  have hEclosed : IsClosed (E : Set K.field.toSubgroup) := by
    have hcarrier : (E : Set K.field.toSubgroup) =
        ((fun x : K.field.toSubgroup => (x : G)) ⁻¹' (L : Set G)) := by
      rfl
    rw [hcarrier]
    exact L.isClosed'.preimage continuous_subtype_val
  let : E.FiniteIndex :=
    @Subgroup.finiteIndex_of_finite_quotient K.field.toSubgroup _ E hLfinite
  have hEopen : IsOpen (E : Set K.field.toSubgroup) :=
    E.isOpen_of_isClosed_of_finiteIndex hEclosed
  change IsClosed
    ((QuotientGroup.mk' (D.extensionInertiaWithin K.field L hLK)) ''
      (E : Set K.field.toSubgroup))
  exact (D.extensionImageInInertiaQuotient K.field L hLK).isClosed_of_isOpen
    (QuotientGroup.isOpenMap_coe
      (N := D.extensionInertiaWithin K.field L hLK)
      (E : Set K.field.toSubgroup) hEopen)

/-- If a Frobenius lift restricts trivially to `L`, its fixed field contains
`L` (equivalently `G_Σ ≤ G_L`). -/
theorem frobeniusFixedField_le_of_restriction_eq_one
    (D : DegreeData G) [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup)]
    (σ : D.FrobeniusElements K L hLK)
    (hσ : D.frobeniusRestriction K L hLK σ = 1) :
    D.frobeniusFixedField_le_of_restriction_eq_oneStatement K L hLK σ hσ := by
  show (D.frobeniusFixedField K L hLK σ).toSubgroup ≤ L.toSubgroup
  let H := D.extensionInertiaWithin K.field L hLK
  let E := L.toSubgroup.subgroupOf K.field.toSubgroup
  let Q := K.field.toSubgroup ⧸ H
  let J : Subgroup Q := D.extensionImageInInertiaQuotient K.field L hLK
  have hσJ : σ.1 ∈ J := by
    let k : K.field.toSubgroup := Quotient.out σ.1
    have hkq : QuotientGroup.mk k = σ.1 := Quotient.out_eq' σ.1
    have hkE : k ∈ E := by
      have hq : (QuotientGroup.mk k :
          K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup) = 1 := by
        change D.extensionRestriction K.field L hLK
          (QuotientGroup.mk k : K.field.toSubgroup ⧸ H) = 1
        rw [hkq]
        exact hσ
      simpa using QuotientGroup.eq.mp hq.symm
    exact ⟨k, hkE, hkq⟩
  have hClosureJ :
      (D.frobeniusClosure K L hLK σ).toSubgroup ≤ J := by
    change (Subgroup.closure (Set.range (fun _ : Unit => σ.1))).topologicalClosure ≤ J
    apply Subgroup.topologicalClosure_minimal
    · rw [Subgroup.closure_le]
      rintro q ⟨u, rfl⟩
      exact hσJ
    · exact extensionImageInInertiaQuotient_isClosed_aux D K L hLK
  rintro g ⟨k, hkClosure, rfl⟩
  have hkJ : (QuotientGroup.mk k : Q) ∈ J := hClosureJ hkClosure
  rcases hkJ with ⟨e, heE, heq⟩
  have hdiff : e⁻¹ * k ∈ H := QuotientGroup.eq.mp heq
  have hdiffE : e⁻¹ * k ∈ E := hdiff.1
  have hkE : k ∈ E := by
    have := E.mul_mem heE hdiffE
    simpa [mul_assoc] using this
  change (k : G) ∈ L
  exact hkE

end DegreeData

end

end Langlands.NYLL.ClassFormation
