import Langlands.GroupScheme.Absolute.TorusFixedCosetBound
import Langlands.GroupScheme.Rational.RankOneWeylQuotient
import Langlands.GroupScheme.Dynamic.FlagQuotientSchemeAction
import Langlands.GroupScheme.SchemeActionRationalOrbit
import Mathlib.Topology.KrullDimension
import Mathlib.Data.ENat.SuccOrder

/-! # Fixed points of a prescribed homogeneous quotient in rank at most one -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace SchemeAction

variable {k : Type u} [Field k]
  {H : GroupScheme (Spec (CommRingCat.of k))}
  {X : Over (Spec (CommRingCat.of k))}

/-- An injection of all-test fixed rational points into two signs gives
dimension at most one, provided dimension at least two would give three
distinct such fixed points. The latter geometric implication is an input. -/
theorem topologicalKrullDim_le_one_of_fixedPointSignEmbedding
    (a : SchemeAction H X)
    (e : {x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X // a.IsFixed x} ↪ Bool)
    (hthree : (2 : WithBot ℕ∞) ≤ topologicalKrullDim X.left →
      Nonempty (Fin 3 ↪
        {x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X // a.IsFixed x})) :
    topologicalKrullDim X.left ≤ 1 := by
  by_contra hdim
  have htwo : (2 : WithBot ℕ∞) ≤ topologicalKrullDim X.left := by
    simpa only [Nat.cast_one, one_add_one_eq_two] using
      (ENat.WithBot.add_one_le_iff (n := 1)).mpr (lt_of_not_ge hdim)
  obtain ⟨f⟩ := hthree htwo
  have hcard : 3 ≤ 2 := by
    simpa using Fintype.card_le_of_injective (f.trans e) (f.trans e).injective
  omega

end SchemeAction

namespace HomogeneousQuotient

variable {k : Type u} [Field k] [IsAlgClosed k]
  {G B : GroupScheme (Spec (CommRingCat.of k))}
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  (hG : IsConnectedReductive G) (i : T.toGrp ⟶ G)
  (hi : IsMaximalTorus i) (hT : IsSplitTorus T.toGrp)
  (hdep : haveI := hG.isAffineHom
    ∀ α ∈ roots i, ∀ β ∈ roots i, ¬ LinearIndependent ℤ ![α, β])
  (b : B ⟶ G) (hb : IsClosedSubgroup b)
  (t : T.toGrp ⟶ B) (ht : t ≫ b = i)
  (hconj : MaximalToriAreConjugate B)
  (hc : centralizerPoints i ≤
    (SubgroupFunctor.range b).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))))
  {Q : Over (Spec (CommRingCat.of k))} (q : G.X ⟶ Q)
  [QuasiCompact q.left] [Flat q.left] [Surjective q.left]
  (hfib : ∀ (V : Over (Spec (CommRingCat.of k))) (g h : V ⟶ G.X),
    g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range b).carrier V)

/-- The all-test torus-fixed rational points of the quotient by the prescribed
subgroup embed into the two signs of the actual rank-one Weyl quotient. -/
def rankOneFixedPointSignEmbedding :
    {x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Q //
      ((Dynamic.flagQuotientSchemeAction G (SubgroupFunctor.range b) q hfib).restrict i).IsFixed x} ↪
        Bool := by
  letI := hG.smooth
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
  let a := (Dynamic.flagQuotientSchemeAction G (SubgroupFunctor.range b) q hfib).restrict i
  have hact : ∀ (V : Over (Spec (CommRingCat.of k)))
      (s : V ⟶ T.toGrp.X) (g : V ⟶ G.X),
      a.act s (g ≫ q) = ((s ≫ i.hom.hom) * g) ≫ q := by
    intro V s g
    rw [SchemeAction.restrict_act, Dynamic.flagQuotientSchemeAction_act_lift]
  exact (torusFixedPointWeylEmbedding i b q hfib hi hb t ht hconj hc a hact hsurj).trans
    (hG.rankOneRelativeWeylQuotientSignEmbedding_of_isMaximalTorus i hi hT hdep)

include hG hi hT hdep hb t ht hconj hc

/-- The prescribed quotient has only finitely many all-test torus-fixed
rational points, under the explicit conjugacy and centralizer inputs. -/
theorem finite_rankOneFixedPoints :
    Finite {x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Q //
      ((Dynamic.flagQuotientSchemeAction G (SubgroupFunctor.range b) q hfib).restrict i).IsFixed x} :=
  Finite.of_injective
    (rankOneFixedPointSignEmbedding hG i hi hT hdep b hb t ht hconj hc q hfib)
    (rankOneFixedPointSignEmbedding hG i hi hT hdep b hb t ht hconj hc q hfib).injective

/-- There are at most two all-test torus-fixed rational points. -/
theorem card_rankOneFixedPoints_le_two :
    Nat.card {x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Q //
      ((Dynamic.flagQuotientSchemeAction G (SubgroupFunctor.range b) q hfib).restrict i).IsFixed x} ≤
        2 := by
  simpa using Nat.card_le_card_of_injective
    (rankOneFixedPointSignEmbedding hG i hi hT hdep b hb t ht hconj hc q hfib)
    (rankOneFixedPointSignEmbedding hG i hi hT hdep b hb t ht hconj hc q hfib).injective

/-- The prescribed rank-one quotient has dimension at most one if dimension
at least two would supply three actual all-test fixed rational points. -/
theorem dimension_le_one_of_three_fixedPoints
    (hthree : (2 : WithBot ℕ∞) ≤ topologicalKrullDim Q.left →
      Nonempty (Fin 3 ↪
        {x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Q //
          ((Dynamic.flagQuotientSchemeAction G (SubgroupFunctor.range b) q hfib).restrict i).IsFixed x})) :
    topologicalKrullDim Q.left ≤ 1 :=
  SchemeAction.topologicalKrullDim_le_one_of_fixedPointSignEmbedding _
    (rankOneFixedPointSignEmbedding hG i hi hT hdep b hb t ht hconj hc q hfib) hthree

end HomogeneousQuotient

end Langlands.GroupScheme
