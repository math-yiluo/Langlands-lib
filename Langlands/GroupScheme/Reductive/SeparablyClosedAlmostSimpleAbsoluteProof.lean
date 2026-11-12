import Langlands.GroupScheme.Reductive.SeparablyClosedAlmostSimpleAbsoluteStatement
import Langlands.GroupScheme.SmoothConnectedNormalClosure
import Langlands.GroupScheme.Rational.TorusGeneratedEnvelopeBaseChange
import Langlands.GroupScheme.Rational.RootSubgroupRealizationProof
import Langlands.GroupScheme.Rational.RootSubgroupNontrivial
import Langlands.GroupScheme.Rational.RootSubgroupBaseChange
import Langlands.GroupScheme.Torus.StrictHenselianMaximalReduction
import Langlands.GroupScheme.Torus.MaximalBaseChangeProof
import Langlands.GroupScheme.Torus.RootSupportBaseChange
import Langlands.GroupScheme.Reductive.NormalRootDichotomyReduction
import Langlands.GroupScheme.Reductive.NormalCenterProof
import Langlands.GroupScheme.Reductive.RootGenerationProof
import Langlands.GroupScheme.Reductive.MinimalNormalFactor
import Langlands.GroupScheme.Reductive.GroundFieldRadical
import Langlands.GroupScheme.Torus.MaximalSplitComparison
import Langlands.GroupScheme.Absolute.RootVectorLineProof
import Langlands.GroupScheme.Absolute.MaximalTorusConjugacyProof
import Langlands.GroupScheme.SimplyConnected.SemisimpleFieldExtensionProof

/-! # Almost-simple groups over separably closed fields are absolutely almost-simple -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

private theorem normalClosure_baseChange_le
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {G U : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [IsAffineHom U.X.hom]
    {j : U ⟶ G} (D : SmoothConnectedNormalClosure j)
    {H : GroupScheme (Spec (CommRingCat.of K))}
    (h : H ⟶ (GroupScheme.baseChange (algebraBaseMap k K)).obj G)
    (hh : IsClosedSubgroup h) (hn : (SubgroupFunctor.range h).IsNormal)
    (hj : SubgroupFunctor.range ((GroupScheme.baseChange (algebraBaseMap k K)).map j) ≤
      SubgroupFunctor.range h) :
    SubgroupFunctor.range ((GroupScheme.baseChange (algebraBaseMap k K)).map D.inclusion) ≤
      SubgroupFunctor.range h := by
  let b := algebraBaseMap k K
  let B := GroupScheme.baseChange b
  let : Smooth D.group.X.hom := D.hasSmoothConnectedGeneration.1
  let : IsAffineHom D.group.X.hom := D.hasSmoothConnectedGeneration.2.1
  obtain ⟨n, _, hdom⟩ := D.hasSmoothConnectedGeneration.2.2.2
  apply EnvelopeBaseChange.range_baseChange_le_of_points K D.toGeneratedImage hdom h hh
  intro W v
  let x := (baseChangePointsEquiv b G W).symm (v ≫ fst G.X U.X)
  let y := (baseChangePointsEquiv b U W).symm (v ≫ snd G.X U.X)
  have hy : y ≫ (B.map j).hom.hom ∈ (SubgroupFunctor.range h).carrier W :=
    hj W (SubgroupFunctor.mem_range.mpr ⟨y, rfl⟩)
  have hc := hn W x (y ≫ (B.map j).hom.hom) (by trivial) hy
  have he : (baseChangePointsEquiv b G W).symm
      (v ≫ SubgroupFunctor.conjugationMap j (𝟙 G)) =
      x * (y ≫ (B.map j).hom.hom) * x⁻¹ := by
    apply (baseChangePointsEquiv b G W).injective
    dsimp only [B]
    simp only [MulEquiv.apply_symm_apply, map_mul, map_inv, x, y,
      baseChangePointsEquiv_comp, SubgroupFunctor.conjugationMap,
      MonObj.comp_mul, GrpObj.comp_inv, Grp.id_hom_hom, Category.comp_id, Category.assoc]
  rw [he]
  exact hc

attribute [local instance]
  P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_geometricallyIntegral.S17A0.subsingleton_spec_field

private theorem exists_full_root_normalClosure
    {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} (hG : IsAlmostSimple G)
    [IsAffineHom G.X.hom]
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (t : T.toGrp ⟶ G)
    (hT : IsSplitTorus T.toGrp) (ht : IsMaximalTorus t)
    (α : characterLattice T) (hα : α ∈ relativeRoots t) :
    ∃ (U : GroupScheme (Spec (CommRingCat.of k))) (j : U ⟶ G)
      (D : SmoothConnectedNormalClosure j),
      (RelativeRoot.subgroup t α).IsRepresentedBy j ∧ IsClosedSubgroup j ∧
        SubgroupFunctor.range D.inclusion = ⊤ := by
  let : Smooth G.X.hom := hG.isSemisimple.isConnectedReductive.smooth
  let : ConnectedSpace G.X.left := hG.isSemisimple.isConnectedReductive.connectedSpace
  obtain ⟨U, j, hj, hclosed, hsmooth, hconn, _, _, _, hLie⟩ :=
    RelativeRoot.rootSubgroupRealization k G hG.isSemisimple.isConnectedReductive
      T t (ht.isMaximalSplitTorus hT) α hα
  let : IsAffineHom U.X.hom := hclosed.isAffineHom
  let : Smooth U.X.hom := hsmooth
  let : ConnectedSpace U.X.left := hconn
  have hnt : RelativeRoot.subgroup t α ≠ ⊥ := by
    intro hz
    have he := (RelativeRoot.hasLieImage_iff_tangentSubmodule_eq _ _).mp hLie
    rw [hz, RelativeRoot.tangentSubmodule_bot] at he
    exact RelativeRoot.positiveWeightSpan_ne_bot t hα he.symm
  let D := smoothConnectedNormalClosure j
  let : GeometricallyConnected D.group.X.hom := D.hasSmoothConnectedGeneration.2.2.1
  have hDconn : ConnectedSpace D.group.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton (f := D.group.X.hom)
  refine ⟨U, j, D, hj, hclosed, ?_⟩
  rcases hG.normalSubgroup_trivial_or_full D.group D.inclusion D.closed
    D.hasSmoothConnectedGeneration.1 hDconn D.isNormal with hz | hfull
  · exfalso
    apply hnt
    rw [← hj.2]
    exact le_antisymm (hz ▸ D.contains) (fun _ => bot_le)
  · exact hfull

private theorem almostSimple_baseChange_of_split_maximalTorus
    {k K : Type u} [Field k] [Field K] [Algebra k K] [IsAlgClosed K]
    {G : GroupScheme (Spec (CommRingCat.of k))} (hG : IsAlmostSimple G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (t : T.toGrp ⟶ G)
    (hT : IsSplitTorus T.toGrp) (ht : IsMaximalTorus t) :
    IsAlmostSimple ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) := by
  let b := algebraBaseMap k K
  let B := GroupScheme.baseChange b
  let GK := B.obj G
  let TK := (CommGroupScheme.baseChange b).obj T
  let tK : TK.toGrp ⟶ GK := B.map t
  let : IsAffineHom G.X.hom := hG.isSemisimple.isConnectedReductive.isAffineHom
  let : Smooth G.X.hom := hG.isSemisimple.isConnectedReductive.smooth
  let : LocallyOfFiniteType G.X.hom := inferInstance
  have hGK : IsSemisimple GK := isSemisimpleFieldExtension k K G hG.isSemisimple
  let : IsAffineHom GK.X.hom := hGK.isConnectedReductive.isAffineHom
  have hTK : IsSplitTorus TK.toGrp := hT.baseChange b
  have htK : IsMaximalTorus tK :=
    (maximalTorusBaseChange k K G T t hT.isTorus ht.2.1).mp ht
  let : Surjective b := (fieldExtension_fpqc k K).1
  let : Flat b := (fieldExtension_fpqc k K).2.1
  let : QuasiCompact b := (fieldExtension_fpqc k K).2.2
  refine ⟨hGK, ?_, ?_⟩
  · apply hGK.noncommutative_of_range_ne_bot
    intro hz
    have hz' : (SubgroupFunctor.range (𝟙 G)).baseChange b = ⊥ := by
      rw [← SubgroupFunctor.range_baseChangeHom, CategoryTheory.Functor.map_id]
      exact hz
    have hbot := SubgroupFunctor.eq_bot_of_baseChange_eq_bot b hz'
    apply hG.noncommutative
    intro W x y
    have hx : x = 1 := by
      have hm : x ∈ (SubgroupFunctor.range (𝟙 G)).carrier W := by
        rw [SubgroupFunctor.range_id]
        trivial
      rwa [hbot, SubgroupFunctor.bot_carrier, Subgroup.mem_bot] at hm
    rw [hx]
    exact Commute.one_left y
  · intro H h hh hs hc hn
    let : Smooth H.X.hom := hs
    let : ConnectedSpace H.X.left := hc
    let : IsAffineHom H.X.hom := hh.isAffineHom
    let : IsClosedImmersion h.hom.hom.left := hh
    let : Mono h.hom.hom := Over.mono_of_mono_left _
    by_cases hfull : SubgroupFunctor.range h = ⊤
    · exact Or.inr hfull
    left
    have hfixed : ∀ β ∈ relativeRoots tK,
        RelativeRoot.subgroup tK β ≤ (AutomorphicAction.conjugation h).fixedSubgroup := by
      intro β hβ
      rcases semisimpleNormalRootDichotomy_of_rootLines normalReductiveCenter
        semisimpleRootGeneration absoluteRootVectorLine maximalTorusConjugacy
        K GK hGK TK tK ⟨hTK, htK.2.1⟩ htK H h hh hn β hβ with hIn | hFix
      · obtain ⟨α, rfl⟩ := (characterLattice.baseChangeEquiv b T hT).surjective β
        have hα : α ∈ relativeRoots t :=
          (mem_roots_baseChange_iff (K := K) G T hT t α).mp hβ
        obtain ⟨U, j, D, hj, hclosed, hD⟩ :=
          exists_full_root_normalClosure hG T t hT ht α hα
        let : IsAffineHom U.X.hom := hclosed.isAffineHom
        have hjK : SubgroupFunctor.range (B.map j) ≤ SubgroupFunctor.range h := by
          dsimp only [B]
          rw [SubgroupFunctor.range_baseChangeHom, hj.2,
            ← RelativeRoot.subgroup_baseChange]
          exact hIn
        have hDK := normalClosure_baseChange_le D h hh hn hjK
        have hDfull : SubgroupFunctor.range (B.map D.inclusion) = ⊤ := by
          dsimp only [B]
          rw [SubgroupFunctor.range_baseChangeHom, hD, SubgroupFunctor.top_baseChange]
        exact (hfull (le_antisymm (fun _ _ _ => Subgroup.mem_top _)
          (hDfull ▸ hDK))).elim
      · exact hFix
    have hcentral : (AutomorphicAction.conjugation h).fixedSubgroup = ⊤ :=
      (AutomorphicAction.conjugation h).fixedSubgroup_eq_top_of_rootGeneration
        semisimpleRootGeneration hGK TK tK ⟨hTK, htK.2.1⟩ htK inferInstance hfixed
    have hH : IsSemisimple H :=
      hGK.of_normalSubgroup_of_normalReductiveCenterStatement normalReductiveCenter h hh hn
    have hcomm : ∀ (W : Over (Spec (CommRingCat.of K))) (x y : W ⟶ H.X), Commute x y := by
      intro W x y
      apply (commute_iff_eq _ _).mpr
      apply (cancel_mono h.hom.hom).mp
      have hm : y ≫ h.hom.hom ∈
          (AutomorphicAction.conjugation h).fixedSubgroup.carrier W := by
        rw [hcentral]
        trivial
      have he := (mem_conjugation_fixedSubgroup_iff h _).mp hm W (𝟙 W) x
      simpa only [Category.id_comp, MonObj.mul_comp] using he.eq
    have hzH : SubgroupFunctor.range (𝟙 H) = ⊥ := by
      by_contra hnt
      exact hH.noncommutative_of_range_ne_bot hnt hcomm
    simpa only [Category.id_comp] using
      (SubgroupFunctor.range_comp_eq_bot_iff (𝟙 H) h).mpr hzH

/-- Milne, Corollary 24.2, including imperfect separably closed fields. -/
theorem separablyClosedAlmostSimpleAbsolute :
    SeparablyClosedAlmostSimpleAbsoluteStatement.{u} := by
  intro k _ _ G hG
  let : Smooth G.X.hom := hG.isSemisimple.isConnectedReductive.smooth
  let : IsAffineHom G.X.hom := hG.isSemisimple.isConnectedReductive.isAffineHom
  obtain ⟨T, t, ht, hT⟩ := exists_isMaximalTorus_isSplitTorus_of_isSepClosed G
  exact ⟨hG, almostSimple_baseChange_of_split_maximalTorus
    (K := AlgebraicClosure k) hG T t hT ht⟩

end Langlands.GroupScheme
