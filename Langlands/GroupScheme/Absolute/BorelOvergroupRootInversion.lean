import Langlands.GroupScheme.Absolute.BorelOvergroupRankOne
import Langlands.GroupScheme.Rational.NormalizerWeightSupport

/-! # Root inversion preserving a Borel overgroup's tangent support -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.AbsoluteBorelOvergroup

variable {k : Type u} [Field k] [IsAlgClosed k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [Smooth G.X.hom] [ConnectedSpace G.X.left]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {P : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth P.X.hom] [ConnectedSpace P.X.left]

/-- If both signs of a root occur in the tangent support, an actual ambient
normalizing point in the overgroup inverts the root and preserves its full
intrinsic tangent-weight support. -/
theorem exists_supportPreserving_rootInverter_of_both_signs
    (hG : IsConnectedReductive G) (hT : IsSplitTorus T.toGrp)
    (j : T.toGrp ⟶ G) (hj : IsMaximalTorus j)
    (i : P ⟶ G) (hi : IsClosedSubgroup i)
    (t : T.toGrp ⟶ P) (ht : t ≫ i = j)
    (α : characterLattice T) (hα : α ∈ roots j)
    (hplus : α ∈ RelativeRoot.actionWeightSupport
      (AutomorphicAction.conjugation j) (SubgroupFunctor.range i))
    (hminus : -α ∈ RelativeRoot.actionWeightSupport
      (AutomorphicAction.conjugation j) (SubgroupFunctor.range i)) :
    haveI := hj.2.1.mono
    ∃ n : normalizerPoints j,
      n.val ∈ (SubgroupFunctor.range i).carrier
        (Over.mk (𝟙 (Spec (CommRingCat.of k)))) ∧
      weylAction j n α = -α ∧
      ∀ β : characterLattice T,
        weylAction j n β ∈ RelativeRoot.actionWeightSupport
          (AutomorphicAction.conjugation j) (SubgroupFunctor.range i) ↔
        β ∈ RelativeRoot.actionWeightSupport
          (AutomorphicAction.conjugation j) (SubgroupFunctor.range i) := by
  let := hj.2.1.mono
  let L := RankOneCentralizerDetection.groupScheme j hT α hα.1
  let l : L ⟶ G := RankOneCentralizerDetection.inclusion j hT α hα.1
  let τ : T.toGrp ⟶ L := RankOneCentralizerDetection.torusHom j hT α hα.1
  have hlc : IsClosedSubgroup l :=
    RankOneCentralizerDetection.isClosedSubgroup_inclusion j hT α hα.1
  have hl : (Dynamic.centralizer (CommGroupScheme.groupHom
      (RankOneCentralizerDetection.cocharacter j hT α hα.1) ≫ j)).IsRepresentedBy l :=
    RankOneCentralizerDetection.isRepresentedBy_inclusion j hT α hα.1
  have hτ : τ ≫ l = j := RankOneCentralizerDetection.torusHom_comp j hT α hα.1
  have hmax : IsMaximalTorus τ := IsMaximalTorus.of_comp hlc (by rwa [hτ])
  let := (RankOneCentralizerDetection.isClosedSubgroup_torusHom j hT α hα.1 hj.2.1).mono
  have hL : IsConnectedReductive L :=
    dynamicCentralizerReductive k G hG _ L l hlc hl
  have hroot : α ∈ roots τ :=
    RootReducedness.mem_roots_torusFactor j
      (RankOneCentralizerDetection.cocharacter j hT α hα.1) hl hα
      (RankOneCentralizerDetection.pairing_cocharacter j hT α hα.1)
  have hcont : SubgroupFunctor.range l ≤ SubgroupFunctor.range i := by
    rw [hl.2]
    exact rankOneCentralizer_le_range_of_both_signs hG hT j hj i hi t ht α hα hplus hminus
  have hstable : (AutomorphicAction.conjugation l).IsStable (SubgroupFunctor.range i) := by
    intro U a g hg
    rw [AutomorphicAction.conjugation_act]
    have ha := hcont U (SubgroupFunctor.mem_range.mpr ⟨a, rfl⟩)
    exact ((SubgroupFunctor.range i).carrier U).mul_mem
      (((SubgroupFunctor.range i).carrier U).mul_mem ha hg)
      (((SubgroupFunctor.range i).carrier U).inv_mem ha)
  obtain ⟨m⟩ := RankOneCentralizerDetection.exists_nonidentityNormalizer j hT hG hj α hα
  let n := normalizerPointsMap τ l j hτ m.val
  refine ⟨n, hcont _ (SubgroupFunctor.mem_range.mpr ⟨m.val.val, rfl⟩), ?_, ?_⟩
  · rw [weylAction_normalizerPointsMap]
    exact hL.weylAction_eq_neg_of_rankOne τ hmax hT
      (RankOneCentralizerDetection.roots_pairwise_dependent j hT α hα.1)
      m.val m.property α hroot
  · intro β
    have h := RelativeRoot.weylAction_mem_actionWeightSupport_iff l τ hstable m.val β
    rw [hτ] at h
    simpa only [n, weylAction_normalizerPointsMap] using h

/-- The Weyl quotient consequently contains a support-preserving root inverter. -/
theorem exists_supportPreserving_weylInverter_of_both_signs
    (hG : IsConnectedReductive G) (hT : IsSplitTorus T.toGrp)
    (j : T.toGrp ⟶ G) (hj : IsMaximalTorus j)
    (i : P ⟶ G) (hi : IsClosedSubgroup i)
    (t : T.toGrp ⟶ P) (ht : t ≫ i = j)
    (α : characterLattice T) (hα : α ∈ roots j)
    (hplus : α ∈ RelativeRoot.actionWeightSupport
      (AutomorphicAction.conjugation j) (SubgroupFunctor.range i))
    (hminus : -α ∈ RelativeRoot.actionWeightSupport
      (AutomorphicAction.conjugation j) (SubgroupFunctor.range i)) :
    haveI := hj.2.1.mono
    ∃ w : relativeWeylGroup j,
      relativeWeylCharacterAction j w α = -α ∧
      ∀ β : characterLattice T,
        relativeWeylCharacterAction j w β ∈ RelativeRoot.actionWeightSupport
          (AutomorphicAction.conjugation j) (SubgroupFunctor.range i) ↔
        β ∈ RelativeRoot.actionWeightSupport
          (AutomorphicAction.conjugation j) (SubgroupFunctor.range i) := by
  let := hj.2.1.mono
  obtain ⟨n, -, hn, hs⟩ := exists_supportPreserving_rootInverter_of_both_signs
    hG hT j hj i hi t ht α hα hplus hminus
  exact ⟨QuotientGroup.mk n, hn, hs⟩

end Langlands.GroupScheme.AbsoluteBorelOvergroup

namespace Langlands.GroupScheme

/-- Internal interface supplying support-preserving root inverters in smooth
connected torus overgroups over algebraically closed fields. -/
def AbsoluteBorelOvergroupRootInversionStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [Smooth G.X.hom] [ConnectedSpace G.X.left],
    IsConnectedReductive G →
    ∀ (T : CommGroupScheme (Spec (CommRingCat.of k)))
      (_hT : IsSplitTorus T.toGrp) (j : T.toGrp ⟶ G) (hj : IsMaximalTorus j)
      (P : GroupScheme (Spec (CommRingCat.of k)))
      [Smooth P.X.hom] [ConnectedSpace P.X.left]
      (i : P ⟶ G), IsClosedSubgroup i →
      ∀ (t : T.toGrp ⟶ P), t ≫ i = j →
      ∀ (α : characterLattice T), α ∈ roots j →
        α ∈ RelativeRoot.actionWeightSupport (AutomorphicAction.conjugation j)
          (SubgroupFunctor.range i) →
        -α ∈ RelativeRoot.actionWeightSupport (AutomorphicAction.conjugation j)
          (SubgroupFunctor.range i) →
        haveI := hj.2.1.mono
        ∃ w : relativeWeylGroup j,
          relativeWeylCharacterAction j w α = -α ∧
          ∀ β : characterLattice T,
            relativeWeylCharacterAction j w β ∈ RelativeRoot.actionWeightSupport
              (AutomorphicAction.conjugation j) (SubgroupFunctor.range i) ↔
            β ∈ RelativeRoot.actionWeightSupport
              (AutomorphicAction.conjugation j) (SubgroupFunctor.range i)

end Langlands.GroupScheme
