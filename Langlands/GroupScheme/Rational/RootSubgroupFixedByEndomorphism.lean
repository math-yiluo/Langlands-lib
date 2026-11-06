import Langlands.GroupScheme.EndomorphismFixedSubgroup
import Langlands.GroupScheme.Rational.RootFactorPairTransport
import Langlands.GroupScheme.Rational.RootFactorizationFromExistence

/-! # Propagating all-test root fixedness by actual opposite factor pairs -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

section OverBase

variable {B : Scheme.{u}} {T : CommGroupScheme B} {G : GroupScheme B}
    (i : T.toGrp ⟶ G) (f : G ⟶ G)

/-- Every point of the actual root functor is fixed by the given endomorphism. -/
def IsFixedBy (a : characterLattice T) : Prop :=
  subgroup i a ≤ endomorphismFixedSubgroup f

/-- An endomorphism fixing the torus preserves each actual root functor. -/
theorem comp_mem_subgroup_of_fixes_torus (hi : i ≫ f = i)
    (a : characterLattice T) {U : Over B} {g : U ⟶ G.X}
    (hg : g ∈ (subgroup i a).carrier U) :
    g ≫ f.hom.hom ∈ (subgroup i a).carrier U := by
  simpa only [hi] using comp_mem_subgroup i a f hg

variable [Mono i.hom.hom.left]

/-- A fixed normalizer point transports fixedness to its Weyl-translated root. -/
theorem IsFixedBy.weylAction {a : characterLattice T}
    (ha : IsFixedBy i f a) (n : normalizerPoints i)
    (hn : n.val ≫ f.hom.hom = n.val) :
    IsFixedBy i f (weylAction i n a) := by
  intro U g hg
  let c := G.constantPoint n.val U
  let h := c⁻¹ * g * c
  have hh : h ∈ (subgroup i a).carrier U :=
    (normalizer_conj_mem_iff i a n h).mp (by
      simpa [h, c, mul_assoc] using hg)
  have hhfix : h ≫ f.hom.hom = h := ha U hh
  have hc : c ≫ f.hom.hom = c := by
    dsimp only [c, constantPoint]
    rw [Category.assoc, hn]
  have he : c * h * c⁻¹ = g := by simp [h, mul_assoc]
  change g ≫ f.hom.hom = g
  rw [← he, MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp, hc, hhfix]

end OverBase

section OppositePairs

variable {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]
    (hT : IsSplitTorus T.toGrp) (f : G ⟶ G) (hi : i ≫ f = i)
    {a : characterLattice T} {x : rationalPoints G}
    {p : rationalPoints G × rationalPoints G}

include hT hi

/-- Uniqueness fixes both ordered opposite factors of a fixed nonidentity root point. -/
theorem IsOppositeFactorPair.map_eq_self_of_fixed
    (ha : a ≠ 0) (hx : x ∈ (subgroup i a).carrier (Over.mk (𝟙 _)))
    (hx1 : x ≠ 1) (hxfix : rationalPoints.map f x = x)
    (hp : IsOppositeFactorPair i a x p) :
    (rationalPoints.map f p.1, rationalPoints.map f p.2) = p := by
  have hmap := hp.map f hi
  rw [hxfix] at hmap
  exact (hp.eq i hT ha hx hx1 hmap).symm

/-- The normalizer represented by such a pair is fixed as an actual rational point. -/
theorem IsOppositeFactorPair.normalizer_fixed_of_fixed
    (ha : a ≠ 0) (hx : x ∈ (subgroup i a).carrier (Over.mk (𝟙 _)))
    (hx1 : x ≠ 1) (hxfix : rationalPoints.map f x = x)
    (hp : IsOppositeFactorPair i a x p) :
    rationalPoints.map f (p.1 * x * p.2) = p.1 * x * p.2 := by
  have he := hp.map_eq_self_of_fixed i hT f hi ha hx hx1 hxfix
  have hfirst : rationalPoints.map f p.1 = p.1 := congrArg Prod.fst he
  have hsecond : rationalPoints.map f p.2 = p.2 := congrArg Prod.snd he
  rw [map_mul, map_mul, hfirst, hsecond, hxfix]

/-- Given a supplied opposite pair, fixedness of a root implies fixedness of its negative. -/
theorem IsFixedBy.neg_of_oppositeFactorPair
    (hfix : IsFixedBy i f a) (ha : a ≠ 0)
    (hx : x ∈ (subgroup i a).carrier (Over.mk (𝟙 _))) (hx1 : x ≠ 1)
    (hp : IsOppositeFactorPair i a x p) : IsFixedBy i f (-a) := by
  have hxfix : rationalPoints.map f x = x := hfix _ hx
  have hnfix := hp.normalizer_fixed_of_fixed i hT f hi ha hx hx1 hxfix
  have hw := hfix.weylAction i f (⟨p.1 * x * p.2, hp.2.2⟩ : normalizerPoints i) hnfix
  rwa [hp.weylAction_eq_neg i hT ha hx hx1] at hw

/-- Existence of actual pairs propagates fixedness to the negative of every root. -/
theorem IsFixedBy.neg [Smooth G.X.hom]
    (hE : HasOppositeFactorPairs i) (ha : a ∈ relativeRoots i)
    (hfix : IsFixedBy i f a) : IsFixedBy i f (-a) := by
  obtain ⟨x, hx, hx1⟩ := exists_rootPoint_actual hT i ha
  obtain ⟨p, hp⟩ := hE a ha x hx hx1
  exact hfix.neg_of_oppositeFactorPair i hT f hi ha.1 hx hx1 hp

end OppositePairs

end Langlands.GroupScheme.RelativeRoot
