import Langlands.GroupScheme.Torus.WeylGroupSchemeQuotientPoints
import Langlands.GroupScheme.SubgroupBaseChange
import Langlands.GroupScheme.SubgroupFunctor.NormalizerBaseChange
import Langlands.GroupScheme.Torus.MaximalBaseChangeForwardReduction

/-! # Base change of represented Weyl quotients -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section BaseChange

variable {S S' : Scheme.{u}} (b : S' ⟶ S)
  {T : CommGroupScheme S} {G N W : GroupScheme S}
  (t : T.toGrp ⟶ G) {n : N ⟶ G}

/-- A represented torus normalizer remains the actual represented normalizer
after arbitrary base change. -/
theorem torusNormalizer_isRepresentedBy_baseChange
    (hn : (torusNormalizer t).IsRepresentedBy n) :
    (torusNormalizer (T := (CommGroupScheme.baseChange b).obj T)
      ((GroupScheme.baseChange b).map t)).IsRepresentedBy
        ((GroupScheme.baseChange b).map n) := by
  unfold torusNormalizer
  rw [SubgroupFunctor.range_baseChangeHom, ← SubgroupFunctor.normalizer_baseChange]
  exact hn.baseChange b

/-- The all-test centralizer-kernel condition for a supplied Weyl quotient
is preserved by arbitrary base change. -/
theorem torusCentralizerKernel_baseChange (q : N ⟶ W)
    (hker : ∀ (U : Over S) (y : U ⟶ N.X),
      y ≫ q.hom.hom = 1 ↔ y ≫ n.hom.hom ∈ (torusCentralizer t).carrier U)
    (U : Over S') (y : U ⟶ ((GroupScheme.baseChange b).obj N).X) :
    y ≫ ((GroupScheme.baseChange b).map q).hom.hom = 1 ↔
      y ≫ ((GroupScheme.baseChange b).map n).hom.hom ∈
        (torusCentralizer (T := (CommGroupScheme.baseChange b).obj T)
          ((GroupScheme.baseChange b).map t)).carrier U := by
  rw [← (baseChangePointsEquiv b W U).injective.eq_iff,
    baseChangePointsEquiv_comp, map_one, hker, torusCentralizer_baseChange,
    SubgroupFunctor.mem_baseChange, baseChangePointsEquiv_comp]

end BaseChange

section FieldFibres

variable {S : Scheme.{u}} {k : Type u} [Field k] [IsAlgClosed k]
  (b : Spec (CommRingCat.of k) ⟶ S)
  {T : CommGroupScheme S} {G N W : GroupScheme S}
  (t : T.toGrp ⟶ G) [Mono t.hom.hom.left]
  {n : N ⟶ G} (hn : (torusNormalizer t).IsRepresentedBy n)
  (q : N ⟶ W) (hq : Surjective q.hom.hom.left)
  [LocallyOfFiniteType N.X.hom] [LocallyOfFiniteType W.X.hom]
  (hker : ∀ (U : Over S) (y : U ⟶ N.X),
    y ≫ q.hom.hom = 1 ↔ y ≫ n.hom.hom ∈ (torusCentralizer t).carrier U)

/-- The rational Weyl group on an algebraically closed field fibre identifies
with rational points of the pulled-back quotient. -/
def fibreRelativeWeylGroupQuotientPointsEquiv :
    relativeWeylGroup (T := (CommGroupScheme.baseChange b).obj T)
      ((GroupScheme.baseChange b).map t) ≃*
        rationalPoints ((GroupScheme.baseChange b).obj W) := by
  have : Mono ((GroupScheme.baseChange b).map t).hom.hom.left :=
    MorphismProperty.overPullbackMap (P := MorphismProperty.monomorphisms _) b t.hom.hom
      inferInstance
  have : LocallyOfFiniteType ((GroupScheme.baseChange b).obj N).X.hom := by
    change LocallyOfFiniteType (Limits.pullback.snd N.X.hom b)
    infer_instance
  have : LocallyOfFiniteType ((GroupScheme.baseChange b).obj W).X.hom := by
    change LocallyOfFiniteType (Limits.pullback.snd W.X.hom b)
    infer_instance
  exact relativeWeylGroupQuotientPointsEquiv ((GroupScheme.baseChange b).map t)
    (T := (CommGroupScheme.baseChange b).obj T)
    (G := (GroupScheme.baseChange b).obj G)
    (N := (GroupScheme.baseChange b).obj N)
    (W := (GroupScheme.baseChange b).obj W)
    (n := (GroupScheme.baseChange b).map n)
    (torusNormalizer_isRepresentedBy_baseChange b t hn)
    ((GroupScheme.baseChange b).map q)
    (MorphismProperty.overPullbackMap (P := @Surjective) b q.hom.hom hq)
    (torusCentralizerKernel_baseChange b t q hker)

include hn q hq hker in
theorem natCard_fibreQuotientPoints_eq_relativeWeylGroup :
    Nat.card (rationalPoints ((GroupScheme.baseChange b).obj W)) =
      Nat.card (relativeWeylGroup (T := (CommGroupScheme.baseChange b).obj T)
        ((GroupScheme.baseChange b).map t)) :=
  Nat.card_congr (fibreRelativeWeylGroupQuotientPointsEquiv b t hn q hq hker).symm.toEquiv

end FieldFibres

end Langlands.GroupScheme
