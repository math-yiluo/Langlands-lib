import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteDomainIdealDescentProof
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainBoundedMapGluing
import Langlands.Geometry.Analytic.SpecialCoverIntersectionQuotient

/-! # Norm-controlled gluing of classes modulo compatible closed ideals -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.Domain.FiniteCover

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : PresentedAffinoidAlgebra K} (c : FiniteCover (Domain.whole K A))
  (I : ∀ i : Fin c.size, Ideal (c.obj i).algebra)

/-- The representatives have equal residues on every actual intersection. -/
def ResidueCompatible (z : ∀ i : Fin c.size, (c.obj i).algebra) : Prop :=
  ∀ i j, ((c.obj i).interLeft (c.obj j)).restriction (z i) -
    ((c.obj i).interRight (c.obj j)).restriction (z j) ∈
      ((c.obj i).interLeft (c.obj j)).restriction.closedIdealMap (I i)

/-- Compatible residue classes on a finite whole-spectrum cover lift to the
original algebra with a uniform bound in the norm of the local representatives. -/
theorem exists_residue_lift (hclosed : ∀ i, IsClosed (I i : Set (c.obj i).algebra))
    (hI : c.IdealCompatible I) :
    ∃ M > 0, ∀ z : ∀ i : Fin c.size, (c.obj i).algebra, c.ResidueCompatible I z →
      ∃ a : A, (∀ i, (c.map i).restriction a - z i ∈ I i) ∧ ‖a‖ ≤ M * ‖z‖ := by
  let J : Ideal A := c.idealContraction I
  let : IsClosed (J : Set A) := c.isClosed_idealContraction I hclosed
  let q := ClosedQuotient.map A J
  let cq := c.pullbackWhole q
  have hmap (i : Fin c.size) : (c.map i).restriction = (c.obj i).baseMap :=
    (c.map i).comp_baseMap
  have hlocal (i : Fin c.size) : (c.obj i).baseMap.closedIdealMap J = I i := by
    rw [← hmap i]
    exact idealEffectiveness K A _ c I hclosed hI i
  have hker (W : Domain K A) (x : W.algebra) :
      Domain.pullbackMap q W x = 0 ↔ x ∈ W.baseMap.closedIdealMap J := by
    change x ∈ RingHom.ker (AffinoidPushout.rightMap q W.baseMap).toAlgHom.toRingHom ↔ _
    rw [ClosedQuotient.ker_rightMap W.baseMap J]
  have hrestriction (i : Fin c.size) (W : Domain K A) (p : W ⟶ c.obj i) :
      p.restriction.closedIdealMap (I i) = W.baseMap.closedIdealMap J := by
    rw [← hlocal i, BoundedAlgHom.closedIdealMap_comp, p.comp_baseMap]
  have htransport (i : Fin c.size) (W : Domain K A) (p : W ⟶ c.obj i) (x : (c.obj i).algebra) :
      (Domain.pullbackRestriction q p).restriction (Domain.pullbackMap q (c.obj i) x) =
        Domain.pullbackMap q W (p.restriction x) :=
    congrArg (fun f : BoundedAlgHom K (c.obj i).algebra (Domain.pullback q W).algebra => f x)
      (Domain.pullbackRestriction_comp_pullbackMap q p)
  obtain ⟨L, hL, hlift⟩ := q.isAdmissibleEpi_iff_normControlledLifts.mp
    (ClosedQuotient.map_isAdmissibleEpi A J)
  let M := L * cq.algebraRestrictionBound
  have hM : 0 < M := mul_pos hL cq.algebraRestrictionBound_pos
  refine ⟨M, hM, fun z hz => ?_⟩
  let w (i : Fin cq.size) : (cq.obj i).algebra := Domain.pullbackMap q (c.obj i) (z i)
  have hw : cq.AlgebraCompatible w := by
    intro i j W p s
    let E := (c.obj i).inter (c.obj j)
    let pi := (c.obj i).interLeft (c.obj j)
    let pj := (c.obj i).interRight (c.obj j)
    let qi := Domain.pullbackRestriction q pi
    let qj := Domain.pullbackRestriction q pj
    let h := Domain.inclusionOfSubset W (Domain.pullback q E)
      (fun _ hx => ⟨p.subset hx, s.subset hx⟩)
    have hpi : h ≫ qi = p := @Subsingleton.elim (Inclusion W (cq.obj i)) inferInstance _ _
    have hpj : h ≫ qj = s := @Subsingleton.elim (Inclusion W (cq.obj j)) inferInstance _ _
    have hmem := hz i j
    change pi.restriction (z i) - pj.restriction (z j) ∈ pi.restriction.closedIdealMap (I i) at hmem
    rw [hrestriction i E pi] at hmem
    have he : Domain.pullbackMap q E (pi.restriction (z i)) =
        Domain.pullbackMap q E (pj.restriction (z j)) := by
      apply sub_eq_zero.mp
      rw [← map_sub (Domain.pullbackMap q E).toAlgHom]
      exact (hker E _).mpr hmem
    have hpq : qi.restriction (w i) = qj.restriction (w j) :=
      (htransport i E pi (z i)).trans (he.trans (htransport j E pj (z j)).symm)
    calc
      _ = h.restriction (qi.restriction (w i)) :=
        congrArg (fun f : Inclusion W (cq.obj i) => f.restriction (w i)) hpi.symm
      _ = h.restriction (qj.restriction (w j)) := congrArg h.restriction hpq
      _ = _ := congrArg (fun f : Inclusion W (cq.obj j) => f.restriction (w j)) hpj
  let y := cq.algebraGlue w hw
  have hy : cq.algebraRestrict y = w := cq.algebraRestrict_glue w hw
  obtain ⟨a, ha, han⟩ := hlift y
  refine ⟨a, fun i => ?_, ?_⟩
  · rw [← hlocal i]
    apply (hker (c.obj i) _).mp
    rw [map_sub (Domain.pullbackMap q (c.obj i)).toAlgHom]
    apply sub_eq_zero.mpr
    calc
      _ = ((cq.map i).restriction) (q a) := by
        rw [hmap i]
        exact congrArg (fun f : BoundedAlgHom K A (cq.obj i).algebra => f a)
          (Domain.pullbackMap_comp_baseMap q (c.obj i))
      _ = (cq.algebraRestrict y) i := congrArg ((cq.map i).restriction) ha
      _ = _ := congrFun hy i
  · have hwn : ‖w‖ ≤ ‖z‖ := by
      apply (pi_norm_le_iff_of_nonneg (norm_nonneg z)).2
      intro i
      exact (AffinoidPushout.norm_rightMap_le q (c.obj i).baseMap (z i)).trans (norm_le_pi_norm z i)
    calc
      ‖a‖ ≤ L * ‖y‖ := han
      _ ≤ L * (cq.algebraRestrictionBound * ‖cq.algebraRestrict y‖) :=
        mul_le_mul_of_nonneg_left (cq.norm_le_algebraRestrictionBound y) hL.le
      _ = M * ‖w‖ := by rw [hy, ← mul_assoc]
      _ ≤ M * ‖z‖ := mul_le_mul_of_nonneg_left hwn hM.le

end Langlands.Analytic.PresentedAffinoidAlgebra.Domain.FiniteCover
