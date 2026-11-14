import Langlands.GroupScheme.Rational.SmoothRootQuotient
import Langlands.GroupScheme.Rational.RootSubgroupStability
import Langlands.GroupScheme.Rational.PositiveSourceContraction
import Langlands.GroupScheme.Rational.TorusUnipotentQuotientConjugacy
import Langlands.GroupScheme.Unipotent.PerfectFieldSplitProof
import Langlands.GroupScheme.Dynamic.UnipotentUnipotenceProof
import Langlands.GroupScheme.Rational.CyclicRootFunctorComparisonProof
import Langlands.GroupScheme.Rational.WeightSupportCongruence

/-! # Perfect-field lifting through actual smooth root maps -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace AutomorphicAction

variable {k : Type u} [Field k]
    {U K : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom U.X.hom] [Smooth K.X.hom]
    (e : AutomorphicAction (Gm (Spec (CommRingCat.of k))).toGrp U)
    (htop : e.unipotent = ⊤)
    (j : K ⟶ U) (hj : IsClosedSubgroup j)
    (hst : e.IsStable (SubgroupFunctor.range j))

include htop hj hst

/-- A smooth closed invariant subgroup of a contracted affine group is
itself connected and unipotent. Its connectedness is proved by contraction,
not inferred from connectedness of the ambient group. -/
theorem connected_unipotent_of_closed_stable_of_contraction :
    ConnectedSpace K.X.left ∧ IsUnipotent K := by
  let : IsClosedImmersion j.hom.hom.left := hj
  let : Mono j.hom.hom := Over.mono_of_mono_left _
  let : IsAffineHom K.X.hom := hj.isAffineHom
  let d := e.onRepresentedSubgroup j ⟨inferInstance, rfl⟩ hst
  have hdj : d.IsEquivariant e j :=
    fun _ _ => e.onRepresentedSubgroup_act_comp j ⟨inferInstance, rfl⟩ hst _ _
  have hdtop : d.unipotent = ⊤ := by
    rw [hdj.unipotent_eq_comap_of_isClosedSubgroup hj, htop]
    apply SubgroupFunctor.ext
    intro V
    apply Subgroup.ext
    intro x
    rfl
  have hrep : d.unipotent.IsRepresentedBy (𝟙 K) := by
    rw [hdtop]
    exact SubgroupFunctor.top_isRepresentedBy_id K
  have hconn := Affine.connectedSpace_of_isRepresentedBy_unipotent d hrep
  let : IsAffineHom (Gm (Spec (CommRingCat.of k))).X.hom := isSplitTorus_gm.isAffineHom
  let : Smooth (Gm (Spec (CommRingCat.of k))).X.hom := smooth_gm _
  have hsemi := d.semidirect_unipotent_map (𝟙 _)
  simp only [restrict_id, hdtop, SubgroupFunctor.map_top, Category.id_comp] at hsemi
  have hsemirep : (Dynamic.unipotent d.semidirectInr).IsRepresentedBy d.semidirectInl :=
    ⟨inferInstance, hsemi⟩
  exact ⟨hconn, dynamicUnipotentUnipotence k d.semidirectProduct d.semidirectInr
    K d.semidirectInl hsemirep⟩

end AutomorphicAction

namespace RelativeRoot

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
    [Smooth G.X.hom] [Smooth H.X.hom]
    (i : T.toGrp ⟶ G) (a : characterLattice T) (q : G ⟶ H)
    (hT : IsSplitTorus T.toGrp) (ha : a ≠ 0)
    (hq : Smooth q.hom.hom.left)
    {U V : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom U.X.hom] [IsAffineHom V.X.hom]
    {jU : U ⟶ G} {jV : V ⟶ H}
    (hU : (subgroup i a).IsRepresentedBy jU)
    (hV : (subgroup (i ≫ q) a).IsRepresentedBy jV)

include hT ha hq

/-- The full scheme-theoretic kernel of the smooth map on root
representatives is connected and unipotent. -/
theorem rootMap_kernel_connected_unipotent :
    ConnectedSpace (kernel (rootMap i a q hU hV)).X.left ∧
      IsUnipotent (kernel (rootMap i a q hU hV)) := by
  let f := rootMap i a q hU hV
  let : Smooth U.X.hom := smooth_of_isRepresentedBy_subgroup hT i a ha hU
  let : Smooth V.X.hom := smooth_of_isRepresentedBy_subgroup hT (i ≫ q) a ha hV
  let : ConnectedSpace U.X.left :=
    connected_of_isRepresentedBy_subgroup hT i a ha dynamicConnected hU
  let : Smooth f.hom.hom.left := (rootMap_smooth_surjective i a q hT ha hq hU hV).1
  let : Smooth (kernel f).X.hom :=
    MorphismProperty.of_isPullback (kernel_isPullback_scheme f) inferInstance
  let : Mono jU.hom.hom := hU.1
  let : Mono jV.hom.hom := hV.1
  let dU := subgroupAction i a jU hU
  let dV := subgroupAction (i ≫ q) a jV hV
  have heU : dU.IsEquivariant (AutomorphicAction.conjugation i) jU :=
    fun _ _ => AutomorphicAction.onRepresentedSubgroup_act_comp
      (AutomorphicAction.conjugation i) jU hU (subgroup_isStable i a) _ _
  have hsupp : actionWeightSupport dU ⊤ ⊆ cyclicTail a 1 := by
    rw [← actionWeightSupport_map jU hU.1 dU (AutomorphicAction.conjugation i)
      (fun _ s x => heU s x) ⊤, SubgroupFunctor.map_top, hU.2]
    exact actionWeightSupport_subset_of_tangentSubmodule_le
      (AutomorphicAction.conjugation i) hT (cyclicTail a 1) (subgroup i a)
      (le_of_eq (tangentSubmodule_subgroup i a hT ha))
  obtain ⟨D, hD, ν, hν⟩ := hT.exists_pairing_eq_pos ha
  have hapos : 0 < latticePairing T a ν := by
    rw [hν]
    exact_mod_cast hD
  have hweights : ∀ c, actionWeightSpace dU c ≠ ⊥ → 0 < latticePairing T c ν := by
    intro c hc
    obtain ⟨n, _, hn, rfl⟩ :=
      hsupp ((mem_actionWeightSupport_top_iff dU c).mpr hc)
    have hn' : 0 < (n : ℤ) := by exact_mod_cast hn
    simpa only [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul] using mul_pos hn' hapos
  let e := dU.restrict (CommGroupScheme.groupHom ν)
  have hetop : e.unipotent = ⊤ :=
    dU.unipotent_eq_top_of_source_weights hT ν hweights
  have hf : dU.IsEquivariant dV f := by
    intro Z s x
    apply (cancel_mono jV.hom.hom).mp
    have heV : dV.IsEquivariant (AutomorphicAction.conjugation (i ≫ q)) jV :=
      fun _ _ => AutomorphicAction.onRepresentedSubgroup_act_comp
        (AutomorphicAction.conjugation (i ≫ q)) jV hV (subgroup_isStable (i ≫ q) a) _ _
    have hcomp := congrArg (fun g : U ⟶ H => x ≫ g.hom.hom)
      (rootMap_comp i a q hU hV)
    have hcomp' := congrArg (fun g : U ⟶ H => dU.act s x ≫ g.hom.hom)
      (rootMap_comp i a q hU hV)
    simp only [Grp.comp_hom_hom] at hcomp hcomp'
    calc
      (dU.act s x ≫ f.hom.hom) ≫ jV.hom.hom =
          (dU.act s x ≫ jU.hom.hom) ≫ q.hom.hom := by
        simpa only [f, Category.assoc] using hcomp'
      _ = (AutomorphicAction.conjugation i).act s (x ≫ jU.hom.hom) ≫ q.hom.hom := by
        rw [heU]
      _ = (AutomorphicAction.conjugation (i ≫ q)).act s
          ((x ≫ f.hom.hom) ≫ jV.hom.hom) := by
        rw [show (x ≫ f.hom.hom) ≫ jV.hom.hom =
          (x ≫ jU.hom.hom) ≫ q.hom.hom by simpa only [f, Category.assoc] using hcomp]
        simp only [AutomorphicAction.conjugation_act, MonObj.mul_comp,
          GrpObj.inv_comp, Category.assoc, Grp.comp_hom_hom]
      _ = dV.act s (x ≫ f.hom.hom) ≫ jV.hom.hom := (heV s _).symm
  have hstable : e.IsStable (SubgroupFunctor.range (kernelι f)) := by
    intro Z s x hx
    rw [mem_range_kernelι_iff] at hx ⊢
    change (dU.restrict (CommGroupScheme.groupHom ν)).act s x ≫ f.hom.hom = 1
    rw [AutomorphicAction.restrict_act, hf, hx, AutomorphicAction.act_one]
  exact AutomorphicAction.connected_unipotent_of_closed_stable_of_contraction
    e hetop (kernelι f) (kernelι_isClosedImmersion f) hstable

include hT ha hq in
/-- Over a perfect field the actual smooth map on root representatives
is surjective on rational points, using its full split-unipotent kernel. -/
theorem rootMap_rationalPoints_surjective_of_perfectField [PerfectField k] :
    Function.Surjective (fun (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ U.X) =>
      x ≫ (rootMap i a q hU hV).hom.hom) := by
  let f := rootMap i a q hU hV
  have hfs := rootMap_smooth_surjective i a q hT ha hq hU hV
  let : Smooth f.hom.hom.left := hfs.1
  let : Smooth (kernel f).X.hom :=
    MorphismProperty.of_isPullback (kernel_isPullback_scheme f) inferInstance
  let : IsAffineHom (kernel f).X.hom := by
    rw [← Over.w (kernelι f).hom.hom]
    infer_instance
  have hK := rootMap_kernel_connected_unipotent i a q hT ha hq hU hV
  let : ConnectedSpace (kernel f).X.left := hK.1
  have hsplit : IsSplitUnipotent (kernel f) :=
    perfectFieldUnipotentSplit k (kernel f) inferInstance hK.2
  have hfquot : IsFppfQuotient (SubgroupFunctor.range (kernelι f)) f :=
    ⟨inferInstance, hfs.2, inferInstance, rfl⟩
  intro y
  let : IsAffine (Over.mk (𝟙 (Spec (CommRingCat.of k)))).left :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of k)))
  exact HomogeneousQuotient.fppf_affine_lifts_of_split_unipotent
    (kernelι f) (kernelι_isClosedImmersion f) hsplit f hfquot _ y

omit hU hV [IsAffineHom U.X.hom] [IsAffineHom V.X.hom] in
/-- Every target root point lifts to an actual source root point over a
perfect field, retaining its exact image under the original homomorphism. -/
theorem exists_root_point_lift_of_smooth_of_perfectField [PerfectField k]
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X)
    (hg : g ∈ (subgroup (i ≫ q) a).carrier _) :
    ∃ x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
      x ∈ (subgroup i a).carrier _ ∧ x ≫ q.hom.hom = g := by
  obtain ⟨U, jU, hU, hUc, _, _⟩ :=
    subgroup_has_smooth_closed_representative hT i a ha
  obtain ⟨V, jV, hV, hVc, _, _⟩ :=
    subgroup_has_smooth_closed_representative hT (i ≫ q) a ha
  let : IsAffineHom U.X.hom := hUc.isAffineHom
  let : IsAffineHom V.X.hom := hVc.isAffineHom
  rw [← hV.2] at hg
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hg
  obtain ⟨z, hz⟩ :=
    rootMap_rationalPoints_surjective_of_perfectField i a q hT ha hq hU hV y
  change z ≫ (rootMap i a q hU hV).hom.hom = y at hz
  refine ⟨z ≫ jU.hom.hom, hU.2 ▸ SubgroupFunctor.mem_range.mpr ⟨z, rfl⟩, ?_⟩
  have hc := congrArg (fun f : U ⟶ H => z ≫ f.hom.hom)
    (rootMap_comp i a q hU hV)
  calc
    (z ≫ jU.hom.hom) ≫ q.hom.hom =
        (z ≫ (rootMap i a q hU hV).hom.hom) ≫ jV.hom.hom := by
      simpa only [Grp.comp_hom_hom, Category.assoc] using hc.symm
    _ = y ≫ jV.hom.hom := by rw [hz]

omit hU hV [IsAffineHom U.X.hom] [IsAffineHom V.X.hom] in
/-- Choose an exact source root lift of a specified target root point
over the original perfect field. -/
def perfectFieldRootPointLift [PerfectField k]
    (g : (subgroup (i ≫ q) a).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k))))) :
    {x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X //
      x ∈ (subgroup i a).carrier _ ∧ x ≫ q.hom.hom = g} :=
  ⟨Classical.choose (exists_root_point_lift_of_smooth_of_perfectField
    i a q hT ha hq g g.property),
    Classical.choose_spec (exists_root_point_lift_of_smooth_of_perfectField
      i a q hT ha hq g g.property)⟩

end RelativeRoot

end Langlands.GroupScheme
