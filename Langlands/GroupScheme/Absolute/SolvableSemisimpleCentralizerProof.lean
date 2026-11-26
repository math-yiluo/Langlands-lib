import Langlands.GroupScheme.Absolute.SolvableSemisimpleCentralizerStatement
import Langlands.GroupScheme.Absolute.SolvableSemisimpleCentralizer.Quotient
import Langlands.GroupScheme.AffineNormalSubgroupQuotientProof
import Langlands.GroupScheme.FppfQuotientTargetSmooth
import Langlands.GroupScheme.Absolute.RationalPointClosureSolvable

/-! # The centralizer of a semisimple point in a connected solvable group -/

universe u

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open AlgebraicGeometry
open scoped CategoryTheory.MonObj commutatorElement

namespace Langlands.GroupScheme

open SemisimpleCentralizer

private theorem connected_and_meets_derived_cosets
    {k : Type u} [Field k] [IsAlgClosed k] (m : ℕ)
    (G : GroupScheme (Spec (CommRingCat.of k))) [Smooth G.X.hom] [IsAffineHom G.X.hom]
    [ConnectedSpace G.X.left] (hm : derivedSeries (rationalPoints G) (m + 1) = ⊥)
    (s : rationalPoints G) (hs : SemisimplePoint.IsSemisimple s)
    {C : GroupScheme (Spec (CommRingCat.of k))} (c : C ⟶ G)
    (hc : (G.pointCentralizer s).IsRepresentedBy c) :
    ConnectedSpace C.X.left ∧ ∀ g : rationalPoints G, ∃ z : rationalPoints C,
      g * (rationalPoints.map c z)⁻¹ ∈ derivedSeries (rationalPoints G) 1 := by
  induction m generalizing G C with
  | zero =>
      have : IsCommMonObj G.X := by
        apply isCommMonObj_of_commuting_points
        intro x y
        rw [← commutatorElement_eq_one_iff_mul_comm]
        have h : ⁅x, y⁆ ∈ derivedSeries (rationalPoints G) 1 :=
          Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
        rw [hm] at h
        exact Subgroup.mem_bot.mp h
      have htop : G.pointCentralizer s = ⊤ := by
        ext T x
        rw [G.mem_pointCentralizer]
        exact iff_of_true (mul_comm _ _) (Subgroup.mem_top _)
      have hrep : (G.pointCentralizer s).IsRepresentedBy (𝟙 G) :=
        ⟨inferInstance, (SubgroupFunctor.range_id G).trans htop.symm⟩
      let e := hc.isoOfIsRepresentedBy hrep
      refine ⟨connectedSpace_of_over_iso ((Grp.forget _).mapIso e)
        (inferInstanceAs (ConnectedSpace G.X.left)), fun g => ?_⟩
      have hg : g ∈ (SubgroupFunctor.range c).carrier _ := by
        rw [hc.2, htop]
        exact Subgroup.mem_top _
      obtain ⟨z, hz⟩ := SubgroupFunctor.mem_range.mp hg
      change rationalPoints.map c z = g at hz
      exact ⟨z, by rw [hz, mul_inv_cancel]; exact (derivedSeries (rationalPoints G) 1).one_mem⟩
  | succ m ih =>
      obtain ⟨N, i, hi, hNs, hNc, hNnormal, hNrange⟩ := exists_derived_stage (G := G) (m + 1)
      have : Mono i.hom.hom := hi.mono_overHom
      have : Smooth N.X.hom := hNs
      have : ConnectedSpace N.X.left := hNc
      have : IsAffineHom N.X.hom := hi.isAffineHom
      have : IsCommMonObj N.X := by
        apply isCommMonObj_of_commuting_points
        intro x y
        apply (cancel_mono i.hom.hom).mp
        change rationalPoints.map i (x * y) = rationalPoints.map i (y * x)
        rw [map_mul, map_mul, ← commutatorElement_eq_one_iff_mul_comm]
        have h := Subgroup.commutator_mem_commutator
          (show rationalPoints.map i x ∈ (rationalPoints.map i).range from ⟨x, rfl⟩)
          (show rationalPoints.map i y ∈ (rationalPoints.map i).range from ⟨y, rfl⟩)
        rw [hNrange, ← derivedSeries_succ, hm] at h
        exact Subgroup.mem_bot.mp h
      have hNle : (rationalPoints.map i).range ≤ derivedSeries (rationalPoints G) 1 := by
        rw [hNrange]
        exact derivedSeries_antitone _ (Nat.succ_le_succ (Nat.zero_le m))
      have hGsol : IsSolvableGroupScheme G :=
        (isSolvableGroupScheme_iff_isSolvable_points G).mpr ⟨m + 2, hm⟩
      have hNu := isUnipotent_of_range_le_derived hGsol i hi hNle
      obtain ⟨Q, q, hQft, hQa, hq⟩ := affineNormalSubgroupQuotient k G N i hi hNnormal
      have : Smooth Q.X.hom := hq.smooth_target
      have : IsAffineHom Q.X.hom := hQa
      have : ConnectedSpace Q.X.left := hq.2.1.surj.connectedSpace q.hom.hom.left.continuous
      have hqp := rationalPoints.map_surjective_of_surjective q hq.2.1
      have hQdepth : derivedSeries (rationalPoints Q) (m + 1) = ⊥ := by
        rw [← map_derivedSeries_eq hqp (m + 1), ← hNrange]
        apply le_bot_iff.mp
        rintro _ ⟨x, hx, rfl⟩
        apply Subgroup.mem_bot.mpr
        exact (mem_range_kernelι_iff q x).mp (hq.2.2.2.symm ▸ hx)
      let t := rationalPoints.map q s
      obtain ⟨C', c', hc', hc'closed⟩ := Q.pointCentralizer_isClosedRepresentable t
      have hcclosed := pointCentralizer_closed hc
      have : LocallyOfFiniteType C.X.hom := hcclosed.locallyOfFiniteType
      have : LocallyOfFiniteType C'.X.hom := hc'closed.locallyOfFiniteType
      have : IsAffineHom C.X.hom := hcclosed.isAffineHom
      have : IsAffineHom C'.X.hom := hc'closed.isAffineHom
      have hC' := ih Q hQdepth t (SemisimplePoint.map hs q) c' hc'
      have : ConnectedSpace C'.X.left := hC'.1
      obtain ⟨r, hr, hrpoints, hrker⟩ :=
        exists_centralizer_quotient i hNnormal q hq.2.2.2 hNu hs hi hqp hc hcclosed hc'
      refine ⟨connectedSpace_of_rational_surjective r hrpoints hrker, fun g => ?_⟩
      obtain ⟨w, hw⟩ := hC'.2 (rationalPoints.map q g)
      obtain ⟨z, hz⟩ := hrpoints w
      have helift := congrArg (fun f : C ⟶ Q => rationalPoints.map f z) hr
      rw [pointMap_comp, pointMap_comp, MonoidHom.comp_apply, MonoidHom.comp_apply, hz] at helift
      let v := g * (rationalPoints.map c z)⁻¹
      have hv : rationalPoints.map q v ∈ derivedSeries (rationalPoints Q) 1 := by
        simpa only [v, map_mul, map_inv, helift] using hw
      rw [← map_derivedSeries_eq hqp 1] at hv
      obtain ⟨a, ha, hav⟩ := hv
      have hker : rationalPoints.map q (v * a⁻¹) = 1 := by
        rw [map_mul, map_inv, hav, mul_inv_cancel]
      have hNr : v * a⁻¹ ∈ (rationalPoints.map i).range := by
        change v * a⁻¹ ∈ (SubgroupFunctor.range i).carrier _
        rw [← hq.2.2.2, mem_range_kernelι_iff]
        exact hker
      have h := (derivedSeries (rationalPoints G) 1).mul_mem (hNle hNr) ha
      exact ⟨z, by simpa only [inv_mul_cancel_right] using h⟩

/-- In a smooth connected affine solvable group over an algebraically closed field, the
centralizer of a semisimple point is connected and its product with the unipotent kernel
of the split torus quotient covers the group. -/
theorem solvableSemisimpleCentralizer : SolvableSemisimpleCentralizerStatement.{u} := by
  intro k _ _ G _ _ _ hG s hs C c hc
  let h := (isSolvableGroupScheme_iff_isSolvable_points G).mp hG
  obtain ⟨m, hm⟩ := h.solvable
  have hdepth : derivedSeries (rationalPoints G) (m + 1) = ⊥ := by
    apply le_bot_iff.mp
    rw [← hm]
    exact derivedSeries_antitone _ (Nat.le_succ m)
  have hC := connected_and_meets_derived_cosets m G hdepth s hs c hc
  refine ⟨hC.1, ?_⟩
  obtain ⟨U, T, i, q, hi, hUs, _, hU, _, hq, hT⟩ := solvableTorusQuotient k G hG
  have : IsCommMonObj T.X := IsSplitTorus.isCommMonObj hT
  have : Smooth U.X.hom := hUs
  have : IsAffineHom U.X.hom := hi.isAffineHom
  have hcclosed := pointCentralizer_closed hc
  have : IsAffineHom C.X.hom := hcclosed.isAffineHom
  have : LocallyOfFiniteType C.X.hom := hcclosed.locallyOfFiniteType
  have : IsAffineHom (U.X ⊗ C.X).hom :=
    AutomorphicAction.SectionCoordinateModel.isAffineHom_tensor U.X C.X
  have : LocallyOfFiniteType (U.X ⊗ C.X).hom := by
    rw [Over.tensorObj_hom]
    infer_instance
  refine ⟨U, i, hi, hU, surjective_of_rational_lifts (subgroupMultiplication i c) fun g => ?_⟩
  obtain ⟨z, hz⟩ := hC.2 g
  let v := g * (rationalPoints.map c z)⁻¹
  have hv : v ∈ (SubgroupFunctor.range i).carrier _ :=
    hq.2.2.2 ▸ (mem_range_kernelι_iff q v).mpr (derived_one_le_ker q hz)
  obtain ⟨x, hx⟩ := SubgroupFunctor.mem_range.mp hv
  change x ≫ i.hom.hom = v at hx
  refine ⟨lift x z, ?_⟩
  rw [comp_subgroupMultiplication, hx]
  exact inv_mul_cancel_right _ _

end Langlands.GroupScheme
