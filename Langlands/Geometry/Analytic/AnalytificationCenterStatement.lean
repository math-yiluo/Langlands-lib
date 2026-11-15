import Langlands.Geometry.Analytic.AnalytificationCenter
import Langlands.Geometry.Analytic.SchemeAnalytificationRationalPoints

/-! # Statement: Berkovich's center map is surjective and restricts to charts and rational points -/

universe u v

namespace Langlands.Analytic.SchemeAnalytification

open CategoryTheory _root_.AlgebraicGeometry Topology
open Langlands.AlgebraicGeometry.PointTopology

/-- Statement (Berkovich 1990, Theorem 3.4.1(i) and Remark 3.4.2, with step (2) of the
proof of Theorem 3.4.1; Conrad–Temkin 2009, §4.1, for the Library's polynomial-locus
model): for a complete nonarchimedean nontrivially normed field `K`,

* affine case, for a `K`-algebra `A` with a finite polynomial presentation `P`:
  (1) the center map from the analytification of `A` to the prime spectrum of `A` is
  surjective; (2) the center of the analytic point of a `K`-algebra map `φ : A → K` is
  the kernel of `φ`; (3) the analytic point of `φ` is the only point with that center;
* scheme case, for a scheme `X` locally of finite type over `K`:
  (4) the center map `π` from the glued analytification to `X` is surjective;
  (5) for every affine open `U`, the preimage of `U` under `π` is the image of the
  analytification of `U`; (6) `π` sends the analytic point of a `K`-point of `X` to the
  image in `X` of the closed point of `Spec K`; (7) that analytic point is the only point
  of the glued space with that image under `π`. -/
def AnalytificationCenterStatement : Prop :=
  (∀ (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
      (A : Type v) [CommRing A] [Algebra K A] (P : FinitePolynomialPresentation K A),
      Function.Surjective (AffineAnalytification.center K P) ∧
      (∀ (φ : AlgPoint K A K) (a : A),
        a ∈ (AffineAnalytification.center K P
          (AffineAnalytification.analyticPoint K P φ)).asIdeal ↔ φ a = 0) ∧
      (∀ (φ : AlgPoint K A K) (x : AffineAnalytification.Space K P),
        AffineAnalytification.center K P x =
            AffineAnalytification.center K P (AffineAnalytification.analyticPoint K P φ) →
          x = AffineAnalytification.analyticPoint K P φ)) ∧
  ∀ (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType f],
    Function.Surjective (center K f) ∧
    (∀ U : X.affineOpens,
      center K f ⁻¹' ((U : X.Opens) : Set X) = Set.range (ι K f U)) ∧
    (∀ p : RingPoint K (Over.mk f) K,
      center K f (analyticRationalPoint K f p) = p.left (IsLocalRing.closedPoint K)) ∧
    (∀ (p : RingPoint K (Over.mk f) K) (z : Space K f),
      center K f z = center K f (analyticRationalPoint K f p) →
        z = analyticRationalPoint K f p)

end Langlands.Analytic.SchemeAnalytification
