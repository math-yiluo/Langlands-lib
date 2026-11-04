import Langlands.GroupScheme.Reductive.NormalUnipotentCommutation
import Langlands.GroupScheme.Reductive.NormalUnipotentRadicalIntersectionStatement
import Langlands.GroupScheme.Reductive.AlgebraicallyClosedPseudoReductive
import Langlands.GroupScheme.Reductive.UnipotentRadicalQuotientProof
import Langlands.GroupScheme.Reductive.FixedCenterContainingTorusStatement
import Langlands.GroupScheme.Unipotent.SplitTorusSubgroupHom
import Langlands.GroupScheme.NormalSubgroupQuotientProof
import Langlands.GroupScheme.Rational.TrivialAction
import Langlands.GroupScheme.Derived.CentralIntersectionPullback

/-! # Radical intersection from a torus containing the full centre -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section GeneralBase

variable {B : Scheme.{u}} {G H V : GroupScheme B}

/-- A monic inclusion reflects the range of an included subgroup. -/
theorem range_comp_comap_of_mono (s : V ⟶ H) (i : H ⟶ G) [Mono i.hom.hom] :
    (SubgroupFunctor.range (s ≫ i)).comap i = SubgroupFunctor.range s := by
  apply SubgroupFunctor.ext
  intro T
  apply Subgroup.ext
  intro x
  rw [SubgroupFunctor.mem_comap, SubgroupFunctor.mem_range, SubgroupFunctor.mem_range]
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨v, (cancel_mono i.hom.hom).mp ?_⟩
    simpa only [Grp.comp_hom_hom, Category.assoc] using hv
  · rintro ⟨v, rfl⟩
    exact ⟨v, by rw [Grp.comp_hom_hom, Category.assoc]⟩

end GeneralBase

section CentreContainingTorus

variable {k : Type u} [Field k]
    {G U H : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    [Smooth U.X.hom] [ConnectedSpace U.X.left]
    [Smooth H.X.hom] [ConnectedSpace H.X.left]

/-- A split torus containing the full centre kills the complete intersection
of a normal reductive subgroup with a normal unipotent subgroup. -/
theorem unipotent_comap_eq_bot_of_center_le_splitTorus
    (r : U ⟶ G) (i : H ⟶ G)
    (hr : IsClosedSubgroup r) (hi : IsClosedSubgroup i)
    (hrn : (SubgroupFunctor.range r).IsNormal)
    (hin : (SubgroupFunctor.range i).IsNormal)
    (hU : IsUnipotent U) (hH : IsConnectedReductive H)
    {T₀ : CommGroupScheme (Spec (CommRingCat.of k))}
    (t : T₀.toGrp ⟶ H) (hT : IsSplitTorus T₀.toGrp)
    (ht : IsClosedSubgroup t) (hc : center H ≤ SubgroupFunctor.range t) :
    (SubgroupFunctor.range r).comap i = ⊥ := by
  let : IsClosedImmersion i.hom.hom.left := hi
  let : IsClosedImmersion t.hom.hom.left := ht
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  let : Mono t.hom.hom := Over.mono_of_mono_left _
  let : Mono (t ≫ i).hom.hom := by
    change Mono (t.hom.hom ≫ i.hom.hom)
    infer_instance
  let : IsAffineHom U.X.hom := by
    rw [← r.hom.hom.w]
    let : IsClosedImmersion r.hom.hom.left := hr
    infer_instance
  let : IsAffine U.X.left := isAffine_of_isAffineHom U.X.hom
  let : IsAffineHom T₀.X.hom := hT.isAffineHom
  let : IsAffine T₀.X.left := isAffine_of_isAffineHom T₀.X.hom
  apply SubgroupFunctor.ext
  intro W
  apply Subgroup.ext
  intro x
  constructor
  · intro hx
    have hxcenter := unipotent_comap_le_center_of_normal_reductive
      r i hr hi hrn hin hU hH W hx
    obtain ⟨z, hz⟩ := SubgroupFunctor.mem_range.1 (hc W hxcenter)
    change x ≫ i.hom.hom ∈ (SubgroupFunctor.range r).carrier W at hx
    obtain ⟨u, hu⟩ := SubgroupFunctor.mem_range.1 hx
    have hzu : z ≫ (t ≫ i).hom.hom = u ≫ r.hom.hom := by
      rw [Grp.comp_hom_hom, ← Category.assoc, hz, hu]
    have hz1 := hT.eq_one_of_comp_eq_comp hU hr z u hzu
    change x = 1
    rw [hz1, MonObj.one_comp] at hz
    exact hz.symm
  · intro hx
    change x = 1 at hx
    rw [hx]
    exact ((SubgroupFunctor.range r).comap i).carrier W |>.one_mem

/-- The full scheme-theoretic intersection is canonically the trivial group
when the displayed centre-containing split torus is supplied. -/
def normalUnipotentIntersectionTrivialIso
    (r : U ⟶ G) (i : H ⟶ G)
    (hr : IsClosedSubgroup r) (hi : IsClosedSubgroup i)
    (hrn : (SubgroupFunctor.range r).IsNormal)
    (hin : (SubgroupFunctor.range i).IsNormal)
    (hU : IsUnipotent U) (hH : IsConnectedReductive H)
    {T₀ : CommGroupScheme (Spec (CommRingCat.of k))}
    (t : T₀.toGrp ⟶ H) (hT : IsSplitTorus T₀.toGrp)
    (ht : IsClosedSubgroup t) (hc : center H ≤ SubgroupFunctor.range t) :
    subgroupIntersection i r ≅ Grp.trivial (Over (Spec (CommRingCat.of k))) := by
  let j := subgroupIntersectionFst i r
  let : IsClosedImmersion j.hom.hom.left :=
    isClosedSubgroup_subgroupIntersectionFst i hr
  let : Mono j.hom.hom := Over.mono_of_mono_left _
  have hj : SubgroupFunctor.range j = ⊥ :=
    (range_subgroupIntersectionFst i r).trans
      (unipotent_comap_eq_bot_of_center_le_splitTorus
        r i hr hi hrn hin hU hH t hT ht hc)
  exact (show (⊥ : SubgroupFunctor H).IsRepresentedBy j from
    ⟨inferInstance, hj⟩).isoOfIsRepresentedBy (bot_isRepresentedBy_kernelUnit H)

end CentreContainingTorus

section AlgebraicallyClosed

variable {k : Type u} [Field k] [IsAlgClosed k]
    {G U H : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    [Smooth U.X.hom] [ConnectedSpace U.X.left]
    [Smooth H.X.hom] [ConnectedSpace H.X.left]

/-- Only the trivial-action specialization of the fixed-torus proposition is
needed to make the central unipotent intersection trivial. -/
theorem unipotent_comap_eq_bot_of_fixedCenterContainingTorus
    (hFixed : FixedCenterContainingTorusStatement.{u})
    (r : U ⟶ G) (i : H ⟶ G)
    (hr : IsClosedSubgroup r) (hi : IsClosedSubgroup i)
    (hrn : (SubgroupFunctor.range r).IsNormal)
    (hin : (SubgroupFunctor.range i).IsNormal)
    (hU : IsUnipotent U) (hH : IsConnectedReductive H) :
    (SubgroupFunctor.range r).comap i = ⊥ := by
  obtain ⟨T, t, hT, ht, hc, _⟩ := hFixed k H hH
    (Gm (Spec (CommRingCat.of k))) isSplitTorus_gm
      (AutomorphicAction.trivial _ H)
  exact unipotent_comap_eq_bot_of_center_le_splitTorus
    r i hr hi hrn hin hU hH t hT ht hc

end AlgebraicallyClosed

/-- The fixed centre-containing torus proposition already implies the full
radical-intersection prerequisite for normal smooth connected subgroups. -/
theorem normalUnipotentRadicalIntersection_of_fixedCenterContainingTorus
    (hFixed : FixedCenterContainingTorusStatement.{u}) :
    NormalUnipotentRadicalIntersectionStatement.{u} := by
  intro k _ _ G H _ _ _ _ _ _ i hi hn U V r s hr hs
  let : IsClosedImmersion i.hom.hom.left := hi
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  let : Smooth U.X.hom := hr.smooth
  let : ConnectedSpace U.X.left := hr.connectedSpace
  let : IsAffineHom U.X.hom := by
    rw [← r.hom.hom.w]
    let : IsClosedImmersion r.hom.hom.left := hr.isClosedSubgroup
    infer_instance
  obtain ⟨R, p, hp, hRp⟩ := unipotentRadicalQuotient k H V s hs
  have hR : IsConnectedReductive R := hRp.isConnectedReductive_of_isAlgClosed
  let : Smooth R.X.hom := hR.smooth
  let : IsAffineHom R.X.hom := hR.isAffineHom
  let : ConnectedSpace R.X.left := hR.connectedSpace
  let : Flat p.hom.hom.left := hp.1
  let : Surjective p.hom.hom.left := hp.2.1
  let : QuasiCompact p.hom.hom.left := by
    have h : QuasiCompact (p.hom.hom.left ≫ R.X.hom) := by
      rw [p.hom.hom.w]
      infer_instance
    exact QuasiCompact.of_comp p.hom.hom.left R.X.hom
  obtain ⟨Q, q, hQs, hQa, hq⟩ := normalSubgroupQuotient k G V (s ≫ i)
    (hs.isClosedSubgroup.comp hi) (hs.isNormal_comp i hi hn)
  let : Smooth Q.X.hom := hQs
  let : IsAffineHom Q.X.hom := hQa
  let : Flat q.hom.hom.left := hq.1
  let : Surjective q.hom.hom.left := hq.2.1
  let : QuasiCompact q.hom.hom.left := by
    have h : QuasiCompact (q.hom.hom.left ≫ Q.X.hom) := by
      rw [q.hom.hom.w]
      infer_instance
    exact QuasiCompact.of_comp q.hom.hom.left Q.X.hom
  have hk : (SubgroupFunctor.range (kernelι q)).comap i =
      SubgroupFunctor.range (kernelι p) := by
    rw [hq.2.2.2, hp.2.2.2]
    exact range_comp_comap_of_mono s i
  let j := SubgroupFunctor.quotientSubgroupHom i q p hk.ge
  have hjmono : Mono j.hom.hom :=
    SubgroupFunctor.quotientSubgroupHom_mono i q p hk.ge hk.le
  let : Mono j.hom.hom := hjmono
  have hjsq : i ≫ q = p ≫ j :=
    SubgroupFunctor.quotientSubgroupHom_square i q p hk.ge
  have hjc : IsClosedSubgroup j := HomImage.isClosedSubgroup_of_mono j
  have hjn : (SubgroupFunctor.range j).IsNormal :=
    SubgroupFunctor.isNormal_range_of_fpqc_square i q p j hjsq hn
  obtain ⟨W, w, f, hw, hf, hfflat, hfsurj, hfqc, _, hWs, hWc, hWa⟩ :=
    HomImage.exists_image (r ≫ q)
  let : Smooth W.X.hom := hWs
  let : ConnectedSpace W.X.left := hWc
  let : IsAffineHom W.X.hom := hWa
  let : Flat f.hom.hom.left := hfflat
  let : Surjective f.hom.hom.left := hfsurj
  let : QuasiCompact f.hom.hom.left := hfqc
  let : IsClosedImmersion w.hom.hom.left := hw
  let : Mono w.hom.hom := Over.mono_of_mono_left _
  have hwn : (SubgroupFunctor.range w).IsNormal :=
    SubgroupFunctor.isNormal_range_of_fpqc_square r q f w hf.symm hr.isNormal
  have hWu : IsUnipotent W := hr.isUnipotent.of_flat_surjective f
  have htriv := unipotent_comap_eq_bot_of_fixedCenterContainingTorus
    hFixed w j hw hjc hwn hjn hWu hR
  apply le_antisymm
  · intro T x hx
    change x ≫ i.hom.hom ∈ (SubgroupFunctor.range r).carrier T at hx
    obtain ⟨u, hu⟩ := SubgroupFunctor.mem_range.1 hx
    have hsq' : i.hom.hom ≫ q.hom.hom = p.hom.hom ≫ j.hom.hom :=
      congrArg (fun a => a.hom.hom) hjsq
    have hf' : f.hom.hom ≫ w.hom.hom = r.hom.hom ≫ q.hom.hom :=
      congrArg (fun a => a.hom.hom) hf
    have hpw : (x ≫ p.hom.hom) ∈
        ((SubgroupFunctor.range w).comap j).carrier T := by
      change (x ≫ p.hom.hom) ≫ j.hom.hom ∈ (SubgroupFunctor.range w).carrier T
      apply SubgroupFunctor.mem_range.2
      refine ⟨u ≫ f.hom.hom, ?_⟩
      calc
        (u ≫ f.hom.hom) ≫ w.hom.hom = (u ≫ r.hom.hom) ≫ q.hom.hom := by
          rw [Category.assoc, hf', ← Category.assoc]
        _ = (x ≫ i.hom.hom) ≫ q.hom.hom := by rw [hu]
        _ = (x ≫ p.hom.hom) ≫ j.hom.hom := by
          rw [Category.assoc, hsq', ← Category.assoc]
    rw [htriv, SubgroupFunctor.bot_carrier, Subgroup.mem_bot] at hpw
    rw [← hp.2.2.2]
    exact (mem_range_kernelι_iff p x).2 hpw
  · exact hs.le_comap hr i hi hn

end Langlands.GroupScheme
