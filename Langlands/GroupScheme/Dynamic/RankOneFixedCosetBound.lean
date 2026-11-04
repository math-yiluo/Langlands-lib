import Langlands.GroupScheme.Absolute.TorusFixedCosetBound
import Langlands.GroupScheme.Rational.RankOneWeylQuotient
import Langlands.GroupScheme.Rational.MinimalParabolicContainment
import Langlands.GroupScheme.Dynamic.FlagQuotientSchemeAction
import Langlands.GroupScheme.SchemeActionRationalOrbit

/-! # Fixed points of an actual dynamic quotient in semisimple rank at most one -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Dynamic

variable {k : Type u} [Field k] [IsAlgClosed k]
  {G P : GroupScheme (Spec (CommRingCat.of k))}
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  (hG : IsConnectedReductive G) (i : T.toGrp ⟶ G)
  (hi : IsMaximalTorus i) (hT : IsSplitTorus T.toGrp)
  (hdep : haveI := hG.isAffineHom
    ∀ α ∈ roots i, ∀ β ∈ roots i, ¬ LinearIndependent ℤ ![α, β])
  (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ T.toGrp)
  (j : P ⟶ G) (hj : IsClosedSubgroup j)
  (hP : (parabolic (χ ≫ i)).IsRepresentedBy j)
  (hconj : MaximalToriAreConjugate P)
  {Q : Over (Spec (CommRingCat.of k))} (q : G.X ⟶ Q)
  [QuasiCompact q.left] [Flat q.left] [Surjective q.left]
  (hfib : ∀ (V : Over (Spec (CommRingCat.of k))) (g h : V ⟶ G.X),
    g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range j).carrier V)

include hG hi hT hdep χ hj hP hconj hfib

/-- The all-test torus-fixed rational points of an actual dynamic quotient
embed into the two global signs of the rank-one root-span action. -/
def rankOneFlagQuotientFixedPointSignEmbedding :
    {x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Q //
      ((flagQuotientSchemeAction G (SubgroupFunctor.range j) q hfib).restrict i).IsFixed x} ↪
        Bool := by
  letI := hG.smooth
  have hc : centralizerPoints i ≤
      (SubgroupFunctor.range j).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) := by
    rw [← torusCentralizer_carrier_base i, hP.2]
    exact ((torusCentralizer_le_dynamicCentralizer i χ).trans
      (centralizer_le_parabolic (χ ≫ i))) _
  have hsurj : Function.Surjective
      (fun g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X => g ≫ q) := by
    have : LocallyOfFiniteType (q.left ≫ Q.hom) := by
      rw [Over.w q]
      infer_instance
    have : LocallyOfFiniteType q.left := locallyOfFiniteType_of_comp q.left Q.hom
    intro x
    obtain ⟨g, hg⟩ := exists_rationalPoint_lift_of_mem_range q.left x.left
      (q.left.surjective (x.left (IsLocalRing.closedPoint k)))
    have hgS : g ≫ G.X.hom = 𝟙 (Spec (CommRingCat.of k)) := by
      rw [← Over.w q, ← Category.assoc, hg]
      exact Over.w x
    exact ⟨Over.homMk g hgS, Over.OverMorphism.ext hg⟩
  let a := (flagQuotientSchemeAction G (SubgroupFunctor.range j) q hfib).restrict i
  have hact : ∀ (V : Over (Spec (CommRingCat.of k)))
      (t : V ⟶ T.toGrp.X) (g : V ⟶ G.X),
      a.act t (g ≫ q) = ((t ≫ i.hom.hom) * g) ≫ q := by
    intro V t g
    rw [SchemeAction.restrict_act, flagQuotientSchemeAction_act_lift]
  exact (torusFixedPointWeylEmbedding i j q hfib hi hj
    (parabolicTorusFactor i χ hP) (parabolicTorusFactor_comp i χ hP)
    hconj hc a hact hsurj).trans
      (hG.rankOneRelativeWeylQuotientSignEmbedding_of_isMaximalTorus i hi hT hdep)

/-- There are finitely many actual all-test fixed rational points. -/
theorem finite_rankOneFlagQuotientFixedPoints :
    Finite {x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Q //
      ((flagQuotientSchemeAction G (SubgroupFunctor.range j) q hfib).restrict i).IsFixed x} :=
  Finite.of_injective
    (rankOneFlagQuotientFixedPointSignEmbedding hG i hi hT hdep χ j hj hP hconj q hfib)
    (rankOneFlagQuotientFixedPointSignEmbedding hG i hi hT hdep χ j hj hP hconj q hfib).injective

/-- There are at most two actual all-test torus-fixed rational points. -/
theorem card_rankOneFlagQuotientFixedPoints_le_two :
    Nat.card {x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Q //
      ((flagQuotientSchemeAction G (SubgroupFunctor.range j) q hfib).restrict i).IsFixed x} ≤ 2 := by
  simpa using Nat.card_le_card_of_injective
    (rankOneFlagQuotientFixedPointSignEmbedding hG i hi hT hdep χ j hj hP hconj q hfib)
    (rankOneFlagQuotientFixedPointSignEmbedding hG i hi hT hdep χ j hj hP hconj q hfib).injective

end Langlands.GroupScheme.Dynamic
