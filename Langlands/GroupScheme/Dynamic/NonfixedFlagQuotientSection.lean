import Langlands.GroupScheme.Absolute.TorusFixedCosetBound
import Langlands.GroupScheme.Rational.RankOneWeylQuotient
import Langlands.GroupScheme.Dynamic.FlagQuotientSchemeAction
import Langlands.GroupScheme.SchemeActionRationalOrbit
import Langlands.GroupScheme.SchemeActionFiniteTarget
import Langlands.GroupScheme.SchemeActionQuotientIdentity

/-! # Nonfixed sections of actual homogeneous quotients -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme.Dynamic

variable {k : Type u} [Field k] [IsAlgClosed k]
    {G P : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {Q : Over (Spec (CommRingCat.of k))}

/-- A proper subgroup quotient has a rational lift whose coset is not fixed
by the torus, provided the actual Weyl quotient is finite and maximal tori
are conjugate inside the stabilizer. -/
def nonfixedFlagQuotientLift
    [Smooth G.X.hom] [ConnectedSpace G.X.left]
    [LocallyOfFiniteType Q.hom] [IsSeparated Q.hom]
    (i : T.toGrp ⟶ G) (hi : IsMaximalTorus i)
    [Finite (relativeWeylGroup i)]
    (j : P ⟶ G) (hj : IsClosedSubgroup j)
    (f : T.toGrp ⟶ P) (hf : f ≫ j = i)
    (hc : centralizerPoints i ≤
      (SubgroupFunctor.range j).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))))
    (hconj : MaximalToriAreConjugate P)
    (hproper : SubgroupFunctor.range j ≠ ⊤)
    (q : G.X ⟶ Q) [Flat q.left] [Surjective q.left] [QuasiCompact q.left]
    (hfib : ∀ (V : Over (Spec (CommRingCat.of k))) (g h : V ⟶ G.X),
      g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range j).carrier V) :
    {g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X //
      ¬ ((flagQuotientSchemeAction G (SubgroupFunctor.range j) q hfib).restrict i).IsFixed
        (g ≫ q)} := by
  apply Classical.choice
  by_contra hnone
  let a := flagQuotientSchemeAction G (SubgroupFunctor.range j) q hfib
  have hall : ∀ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
      (a.restrict i).IsFixed (g ≫ q) := by
    intro g
    by_contra hg
    exact hnone ⟨⟨g, hg⟩⟩
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
  have hact : ∀ (V : Over (Spec (CommRingCat.of k)))
      (t : V ⟶ T.toGrp.X) (g : V ⟶ G.X),
      (a.restrict i).act t (g ≫ q) = ((t ≫ i.hom.hom) * g) ≫ q := by
    intro V t g
    rw [SchemeAction.restrict_act, flagQuotientSchemeAction_act_lift]
  have hfixed : ∀ x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Q,
      (a.restrict i).IsFixed x := by
    intro x
    obtain ⟨g, rfl⟩ := hsurj x
    exact hall g
  have : Finite {x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Q //
      (a.restrict i).IsFixed x} :=
    finite_torusFixedPoints i j q hfib hi hj f hf hconj hc
      (a.restrict i) hact hsurj
  have : Finite (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Q) :=
    Finite.of_injective (fun x => (⟨x, hfixed x⟩ :
      {x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Q //
        (a.restrict i).IsFixed x}))
      (fun _ _ he => congrArg Subtype.val he)
  have hGfixed := a.isFixed_of_finite_rationalPoints (quotientIdentityPoint q)
  apply hproper
  apply SubgroupFunctor.ext
  intro V
  apply le_antisymm le_top
  intro g _
  have he := hGfixed V (toUnit V) g
  rw [comp_quotientIdentityPoint, flagQuotientSchemeAction_act_lift, mul_one] at he
  have hm := (hfib V 1 g).mp he.symm
  simpa only [inv_one, one_mul] using hm

/-- In semisimple rank at most one, the actual Weyl sign embedding supplies
the finiteness needed to construct a nonfixed quotient section. -/
def rankOneNonfixedFlagQuotientLift
    (hG : IsConnectedReductive G)
    (i : T.toGrp ⟶ G) (hi : IsMaximalTorus i) (hT : IsSplitTorus T.toGrp)
    (hdep : haveI := hG.isAffineHom
      ∀ α ∈ roots i, ∀ β ∈ roots i, ¬ LinearIndependent ℤ ![α, β])
    (j : P ⟶ G) (hj : IsClosedSubgroup j)
    (f : T.toGrp ⟶ P) (hf : f ≫ j = i)
    (hc : centralizerPoints i ≤
      (SubgroupFunctor.range j).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))))
    (hconj : MaximalToriAreConjugate P)
    (hproper : SubgroupFunctor.range j ≠ ⊤)
    (q : G.X ⟶ Q) [Flat q.left] [Surjective q.left] [QuasiCompact q.left]
    [LocallyOfFiniteType Q.hom] [IsSeparated Q.hom]
    (hfib : ∀ (V : Over (Spec (CommRingCat.of k))) (g h : V ⟶ G.X),
      g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range j).carrier V) :
    {g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X //
      ¬ ((flagQuotientSchemeAction G (SubgroupFunctor.range j) q hfib).restrict i).IsFixed
        (g ≫ q)} := by
  letI := hG.smooth
  letI := hG.connectedSpace
  let e := hG.rankOneRelativeWeylQuotientSignEmbedding_of_isMaximalTorus i hi hT hdep
  letI : Finite (relativeWeylGroup i) := Finite.of_injective e e.injective
  exact nonfixedFlagQuotientLift i hi j hj f hf hc hconj hproper q hfib

end Langlands.GroupScheme.Dynamic
