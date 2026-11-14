import Langlands.GroupScheme.Torus.LocalSplitWeylPointOrder
import Langlands.GroupScheme.Torus.WeylGroupSchemeBaseChange

/-! # Field-valued fibre orders of supplied Weyl quotients -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

/-- Rational points of the pulled-back group are actual lifts of the field-valued
base morphism into its original total scheme. -/
def groupSchemeFibrePointsEquiv {S : Scheme.{u}} {k : Type u} [Field k]
    (b : Spec (CommRingCat.of k) ⟶ S) (W : GroupScheme S) :
    rationalPoints ((baseChange b).obj W) ≃
      {x : Spec (CommRingCat.of k) ⟶ W.X.left // x ≫ W.X.hom = b} where
  toFun y := ⟨y.left ≫ Limits.pullback.fst W.X.hom b, by
    have hy : y.left ≫ Limits.pullback.snd W.X.hom b = 𝟙 _ := y.w
    rw [Category.assoc, Limits.pullback.condition, ← Category.assoc, hy]
    exact Category.id_comp b⟩
  invFun x := Over.homMk
    (Limits.pullback.lift x.val (𝟙 _) (by simpa using x.property))
    (by
      change Limits.pullback.lift x.val (𝟙 _) _ ≫
        Limits.pullback.snd W.X.hom b = 𝟙 _
      simp)
  left_inv y := by
    apply Over.OverMorphism.ext
    apply Limits.pullback.hom_ext
    · simp
    · change Limits.pullback.lift (y.left ≫ Limits.pullback.fst W.X.hom b) (𝟙 _) _ ≫
        Limits.pullback.snd W.X.hom b = y.left ≫ Limits.pullback.snd W.X.hom b
      rw [Limits.pullback.lift_snd]
      exact (show y.left ≫ Limits.pullback.snd W.X.hom b = 𝟙 _ from y.w).symm
  right_inv x := Subtype.ext (by simp)

section SuppliedQuotient

variable {S : Scheme.{u}} {k : Type u} [Field k] [IsAlgClosed k]
  (b : Spec (CommRingCat.of k) ⟶ S)
  {T : CommGroupScheme S} {G N W : GroupScheme S}
  (t : T.toGrp ⟶ G) [Mono t.hom.hom.left]
  {n : N ⟶ G} (hn : (torusNormalizer t).IsRepresentedBy n)
  (q : N ⟶ W) (hq : Surjective q.hom.hom.left)
  [LocallyOfFiniteType N.X.hom] [LocallyOfFiniteType W.X.hom]
  (hker : ∀ (U : Over S) (y : U ⟶ N.X),
    y ≫ q.hom.hom = 1 ↔ y ≫ n.hom.hom ∈ (torusCentralizer t).carrier U)

/-- Actual field-valued lifts into a supplied quotient are the original point
Weyl quotient on that same test scheme. -/
def weylQuotientFibrePointEquiv :
    {x : Spec (CommRingCat.of k) ⟶ W.X.left // x ≫ W.X.hom = b} ≃
      pointWeylGroup t (Over.mk b) := by
  have : Mono ((baseChange b).map t).hom.hom.left :=
    MorphismProperty.overPullbackMap (P := MorphismProperty.monomorphisms _) b t.hom.hom
      inferInstance
  exact (groupSchemeFibrePointsEquiv b W).symm.trans
    (((fibreRelativeWeylGroupQuotientPointsEquiv b t hn q hq hker).symm.trans
      (fibreRelativeWeylGroupEquiv b t)).toEquiv)

end SuppliedQuotient

/-- The field-valued lifts into a supplied Weyl quotient over a split local base
have the common closed-fibre Weyl order. -/
theorem natCard_quotientFibre_eq_localSplitWeylOrder
    {R : Type u} [CommRing R] [IsLocalRing R] (I : Type u) [Fintype I]
    {G N W : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
    [LocallyOfFiniteType N.X.hom] [LocallyOfFiniteType W.X.hom]
    (hG : IsReductive G) (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    (hi : IsClosedSubgroup i)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    {n : N ⟶ G}
    (hn : (torusNormalizer (T := splitTorus.commGroupScheme _ I) i).IsRepresentedBy n)
    (q : N ⟶ W) (hq : Surjective q.hom.hom.left)
    (hker : ∀ (U : Over (Spec (CommRingCat.of R))) (y : U ⟶ N.X),
      y ≫ q.hom.hom = 1 ↔ y ≫ n.hom.hom ∈
        (torusCentralizer (T := splitTorus.commGroupScheme _ I) i).carrier U)
    (k : Type u) [Field k] [IsAlgClosed k] [Algebra R k] :
    Nat.card {x : Spec (CommRingCat.of k) ⟶ W.X.left //
      x ≫ W.X.hom = algebraBaseMap R k} = localSplitWeylOrder I G i := by
  let : IsClosedImmersion i.hom.hom.left := hi
  exact (Nat.card_congr
    (weylQuotientFibrePointEquiv (algebraBaseMap R k)
      (T := splitTorus.commGroupScheme _ I) i hn q hq hker)).trans
      (natCard_pointWeylGroup_eq_localSplitWeylOrder I hG i hi hmax k)

end Langlands.GroupScheme
