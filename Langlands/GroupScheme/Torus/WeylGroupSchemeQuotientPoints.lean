import Langlands.GroupScheme.Rational.TorusNormalizer
import Langlands.GroupScheme.Rational.Characters
import Langlands.GroupScheme.Lie.SurjectiveDifferentialProof

/-! # Algebraically closed points of a represented Weyl quotient -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section RepresentedNormalizer

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G N W : GroupScheme (Spec (CommRingCat.of k))}
  (t : T.toGrp ⟶ G) [Mono t.hom.hom.left]
  {n : N ⟶ G} (hn : (torusNormalizer t).IsRepresentedBy n)

/-- The rational points of a represented normalizer are the normalizing points. -/
def normalizerRationalPointsEquiv : rationalPoints N ≃* normalizerPoints t :=
  (hn.pointsEquiv _).trans (MulEquiv.subgroupCongr (torusNormalizer_carrier_base t))

@[simp] theorem normalizerRationalPointsEquiv_apply_coe (y : rationalPoints N) :
    (normalizerRationalPointsEquiv t hn y : rationalPoints G) = y ≫ n.hom.hom :=
  rfl

theorem normalizerRationalPointsEquiv_symm_comp (x : normalizerPoints t) :
    (normalizerRationalPointsEquiv t hn).symm x ≫ n.hom.hom = x :=
  congrArg Subtype.val ((normalizerRationalPointsEquiv t hn).apply_symm_apply x)

/-- Send a normalizing rational point to the quotient through its represented lift. -/
def normalizerQuotientRationalPointsHom (q : N ⟶ W) :
    normalizerPoints t →* rationalPoints W :=
  (rationalPoints.map q).comp (normalizerRationalPointsEquiv t hn).symm.toMonoidHom

theorem normalizerQuotientRationalPointsHom_ker (q : N ⟶ W)
    (hker : ∀ (U : Over (Spec (CommRingCat.of k))) (y : U ⟶ N.X),
      y ≫ q.hom.hom = 1 ↔ y ≫ n.hom.hom ∈ (torusCentralizer t).carrier U) :
    (normalizerQuotientRationalPointsHom t hn q).ker =
      (centralizerPoints t).subgroupOf (normalizerPoints t) := by
  ext x
  change ((normalizerRationalPointsEquiv t hn).symm x ≫ q.hom.hom = 1) ↔
    (x : rationalPoints G) ∈ centralizerPoints t
  rw [hker, normalizerRationalPointsEquiv_symm_comp, torusCentralizer_carrier_base]

end RepresentedNormalizer

section AlgebraicallyClosed

variable {k : Type u} [Field k] [IsAlgClosed k]
  {N W : GroupScheme (Spec (CommRingCat.of k))}
  [LocallyOfFiniteType N.X.hom] [LocallyOfFiniteType W.X.hom]

/-- A surjective homomorphism between locally finite type group schemes over an
algebraically closed field is surjective on rational points. -/
theorem rationalPoints.map_surjective_of_surjective (q : N ⟶ W)
    (hq : Surjective q.hom.hom.left) : Function.Surjective (rationalPoints.map q) := by
  let := hq
  intro w
  exact Lie.exists_rational_lift_of_mem_range q w
    (q.hom.hom.left.surjective (w.left (IsLocalRing.closedPoint k)))

variable {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  (t : T.toGrp ⟶ G) [Mono t.hom.hom.left]
  {n : N ⟶ G} (hn : (torusNormalizer t).IsRepresentedBy n)
  (q : N ⟶ W) (hq : Surjective q.hom.hom.left)
  (hker : ∀ (U : Over (Spec (CommRingCat.of k))) (y : U ⟶ N.X),
    y ≫ q.hom.hom = 1 ↔ y ≫ n.hom.hom ∈ (torusCentralizer t).carrier U)

/-- The quotient's algebraically closed rational points are `N(k)/Z(k)`, with the
normalizer and centralizer interpreted as the actual torus subgroup functors. -/
def relativeWeylGroupQuotientPointsEquiv :
    relativeWeylGroup t ≃* rationalPoints W :=
  (QuotientGroup.quotientMulEquivOfEq
    (normalizerQuotientRationalPointsHom_ker t hn q hker).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective
        (normalizerQuotientRationalPointsHom t hn q)
        ((rationalPoints.map_surjective_of_surjective q hq).comp
          (normalizerRationalPointsEquiv t hn).symm.surjective))

@[simp] theorem relativeWeylGroupQuotientPointsEquiv_mk (x : normalizerPoints t) :
    relativeWeylGroupQuotientPointsEquiv t hn q hq hker (QuotientGroup.mk x) =
      (normalizerRationalPointsEquiv t hn).symm x ≫ q.hom.hom :=
  rfl

include hn q hq hker in
theorem natCard_quotientPoints_eq_relativeWeylGroup :
    Nat.card (rationalPoints W) = Nat.card (relativeWeylGroup t) :=
  Nat.card_congr (relativeWeylGroupQuotientPointsEquiv t hn q hq hker).symm.toEquiv

end AlgebraicallyClosed

end Langlands.GroupScheme
