import Langlands.GroupScheme.Rational.TrialitarianCubicSplitTorusStatement
import Langlands.GroupScheme.Rational.TrialitarianLeafLeviRootDatum
import Langlands.GroupScheme.Rational.SplitTorusParabolicGaloisComparison
import Langlands.GroupScheme.Reductive.PinningConstruction
import Langlands.GroupScheme.Reductive.RootDatumExistence
import Langlands.GroupScheme.Reductive.RootDatumTorusTransport
import Langlands.GroupScheme.Reductive.SplitRootLieLineProof

/-! # A maximal torus split by the cubic field of a trialitarian group -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.LinearAlgebra

namespace Langlands.GroupScheme

set_option maxHeartbeats 1800000 in
private theorem splitTorusGaloisComparison_of_split
    {F K : Type u} [Field F] [Field K] [CharZero F] [Algebra F K]
    [Algebra K (SeparableClosure F)] [IsScalarTower F K (SeparableClosure F)]
    {M : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom M.X.hom]
    [LocallyOfFiniteType M.X.hom]
    [IsAffineHom ((GroupScheme.baseChange (algebraBaseMap F K)).obj M).X.hom]
    (hM : IsConnectedReductive M) (p : GaloisPinningData F (SeparableClosure F) M)
    {S : CommGroupScheme (Spec (CommRingCat.of K))}
    (s : S.toGrp ⟶ (GroupScheme.baseChange (algebraBaseMap F K)).obj M)
    (hs : IsMaximalTorus s) (hS : IsSplitTorus S.toGrp) :
    SplitTorusGaloisComparison F K (SeparableClosure F) M p s := by
  let MK := (GroupScheme.baseChange (algebraBaseMap F K)).obj M
  have hMK : IsConnectedReductive MK := connectedReductiveFieldExtensionStatement F K M hM
  obtain ⟨J, hJ, P, hP, hred⟩ := rootDatumExistence K MK hMK S hS s hs
  let : Finite J := hJ
  let q := SplitPinning.ofRootDatum hMK hS s hs P hP hred
    (splitRootLieLine K MK hMK S hS s hs)
  obtain ⟨e, _, htransport⟩ :=
    SplitTorusParabolicComparison.exists_rootDatumEquiv_parabolic_galoisComparison q p
  refine q.splitTorusGaloisComparison_of_transport p e (fun τ hτ => ?_) htransport
  apply SplitTorusParabolicComparison.galoisAction_mem_weyl_of_fixes q p τ
  have h := StarActionFiniteStage.algebraBaseMap_comp_galoisBaseMap
    (1 : K ≃ₐ[F] K) τ (fun x => hτ x)
  simpa only [galoisBaseMap_one, Category.comp_id] using h.symm

set_option maxHeartbeats 1800000 in
/-- An anisotropic simply connected trialitarian group split by a cyclic cubic extension
has a maximal torus over the ground field that splits over the same extension. -/
theorem trialitarianCubicSplitMaximalTorus :
    TrialitarianCubicSplitMaximalTorusStatement.{u} := by
  intro F K _ _ _ _ _ _ _ hK H _ _ d q hsc _ _ hD hleaf hsplit
  let E := SeparableClosure F
  let f : K →ₐ[F] E := IsSepClosed.lift
  let : Algebra K E := f.toRingHom.toAlgebra
  let : IsScalarTower F K E := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  let B := GroupScheme.baseChange (algebraBaseMap F K)
  have hH := hsc.isSemisimple.isConnectedReductive
  have : Smooth H.X.hom := hH.smooth
  have hHK := connectedReductiveFieldExtensionStatement F K H hH
  have : IsAffineHom (B.obj H).X.hom := hHK.isAffineHom
  have : Smooth (B.obj H).X.hom := hHK.smooth
  obtain ⟨S, s, hs, hS⟩ := hsplit
  obtain ⟨J, P, hP, e, θ, hroot, hcoroot, hkernel, htrans⟩ :=
    splitTorusGaloisComparison_of_split hH d.pinning s hs hS
  have hstar (τ : E ≃ₐ[F] E)
      (hτ : ∀ x : K, τ (algebraMap K E x) = algebraMap K E x) (a : d.Vertex) :
      d.star τ a = a := by
    have hc := (d.pinning.starAction_eq_one_iff τ).mpr (hkernel τ hτ)
    apply Subtype.ext
    change (d.pinning.starAction τ).val.indexEquiv a.val = a.val
    rw [hc]
    rfl
  obtain ⟨σ, τ, hστ, hσ, hτ0, hτ2, _⟩ := d.exists_star_leafCycle q hD hleaf K hK hstar
  have hcard := (IsGalois.card_aut_eq_finrank F K).trans hK
  obtain ⟨hgen, hσ3, h01, h02, h12⟩ := card_three_generator hcard σ hσ
  obtain ⟨C, j, g, hj, hC, hjK⟩ := d.exists_leafLevi_descent hsc q hD hS s hP e θ hroot htrans
    σ τ hστ hgen hσ3 h01 h02 h12 hτ0 hτ2
  let s' := s ≫ ((B.obj H).innerIso g).hom
  have hs' : IsMaximalTorus s' := hs.comp_iso _
  have hjKclosed : IsClosedSubgroup (B.map j) := hj.baseChange _
  let ζ := θ.symm
    (d4LeafParabolicCoweights d.pinning.toSplitPinning.rootDatum d.pinning.toSplitPinning.base q 0 -
      d4LeafParabolicCoweights d.pinning.toSplitPinning.rootDatum d.pinning.toSplitPinning.base q 1)
  have hrep : (Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ s')).IsRepresentedBy (B.map j) :=
    hjK ▸ hjKclosed.isRepresentedBy_range
  let sC := hrep.factorHom s' (range_le_centralizer_groupHom_comp s' ζ)
  have hsCcomp : sC ≫ B.map j = s' :=
    hrep.factorHom_comp s' (range_le_centralizer_groupHom_comp s' ζ)
  have hsC : IsMaximalTorus sC :=
    IsMaximalTorus.of_comp hjKclosed (hsCcomp.symm ▸ hs')
  have : IsAffineHom C.X.hom := hC.isAffineHom
  have : Smooth C.X.hom := hC.smooth
  have hCK := connectedReductiveFieldExtensionStatement F K C hC
  have : IsAffineHom (B.obj C).X.hom := hCK.isAffineHom
  have : Smooth (B.obj C).X.hom := hCK.smooth
  let pC := GaloisPinningData.ofSeparableClosure hC
  have hcmpC := splitTorusGaloisComparison_of_split hC pC sC hsC hS
  have hcmpC' := hcmpC
  obtain ⟨R, Pc, hPc, ec, θc, hrootc, hcorootc, _, _⟩ := hcmpC'
  have hP' : IsRootDatumOf s' P := hP.comp_iso _
  have : d.pinning.toSplitPinning.rootDatum.IsReduced := d.pinning.isReduced
  obtain ⟨a, b, hab, hba, hcase⟩ := hP'.exists_a2_of_leafCentralizer hPc hS hs'.2.1
    (B.map j) hsCcomp d.pinning.toSplitPinning.base (d.pinning_corootSpan_eq_top hsc)
    q (fun a b => hD a b) e θ hroot hcoroot hrep
  have hpairs (i k : R) : pC.rootDatum.pairing (ec i) (ec k) = Pc.pairing i k := by
    change pC.toSplitPinning.rootDatum.root' (ec i)
      (pC.toSplitPinning.rootDatum.coroot (ec k)) = Pc.root' i (Pc.coroot k)
    rw [← hcorootc, ← hrootc]
  have hcase' (i : pC.rootIndex) :
      ∃ k, pC.rootDatum.coroot i =
        a2Coroots (pC.rootDatum.coroot (ec a)) (pC.rootDatum.coroot (ec b)) k := by
    obtain ⟨i, rfl⟩ := ec.surjective i
    obtain ⟨k, hk⟩ := hcase i
    refine ⟨k, ?_⟩
    change pC.toSplitPinning.rootDatum.coroot (ec i) =
      a2Coroots (pC.toSplitPinning.rootDatum.coroot (ec a))
        (pC.toSplitPinning.rootDatum.coroot (ec b)) k
    simpa only [map_a2Coroots, hcorootc] using congrArg θc hk
  obtain ⟨T, t, ht, hconj⟩ := exists_a2_maximalTorus_descent pC hC sC hsC hS hcmpC
    (ec a) (ec b) ((hpairs a b).trans hab) ((hpairs b a).trans hba) hcase'
    σ τ hστ hgen hσ3 h01 h02 h12
  have hconj' := hconj.postcomp (B.map j)
  rw [hsCcomp, ← B.map_comp] at hconj'
  have hmax : IsMaximalTorus (T := (CommGroupScheme.baseChange (algebraBaseMap F K)).obj T)
      (B.map (t ≫ j)) :=
    hconj'.isMaximalTorus_iff.mpr hs'
  refine ⟨T, t ≫ j, (maximalTorusBaseChange F K H T (t ≫ j) ht.1 (ht.2.1.comp hj)).mpr hmax, ?_⟩
  obtain ⟨_, eT, _⟩ := hconj
  exact IsSplitTorus.of_iso eT hS

end Langlands.GroupScheme
