import Langlands.Geometry.Analytic.AffineAnalytificationSeminorm

/-! # Statement: points of the affine analytification as multiplicative seminorms -/

universe u v

namespace Langlands.Analytic.AffineAnalytification

open Set Topology

/-- Statement (Berkovich 1990, Remark 3.4.2, for `X = Spec A`, with the topology of
Definition 1.5.1): for a complete nonarchimedean nontrivially normed field `K` and a
finite polynomial presentation `P` of a commutative `K`-algebra `A`,
1. the map sending a point `x` of the polynomial-locus analytification `Space K P` to
   the function `a ↦ |a|_x` on `A` is a topological embedding into the product space
   `A → ℝ`; so the points are determined by their seminorms, and the topology of
   `Space K P` is the weakest one making every evaluation `x ↦ |a|_x` continuous;
2. the seminorms of points are exactly the multiplicative seminorms on `A` that extend
   the norm of `K`. -/
def AffineAnalytificationSeminormStatement : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (A : Type v) [CommRing A] [Algebra K A] (P : FinitePolynomialPresentation K A),
    IsEmbedding (fun (x : Space K P) (a : A) => pointSeminorm K P x a) ∧
    range (pointSeminorm K P) = {ν : MulRingSeminorm A | ExtendsNorm K ν}

end Langlands.Analytic.AffineAnalytification
