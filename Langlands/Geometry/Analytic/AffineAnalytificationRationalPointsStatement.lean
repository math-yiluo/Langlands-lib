import Langlands.Geometry.Analytic.AffineAnalytificationRationalPoints

/-! # Statement: rational points of the polynomial-locus analytification -/

universe u v

namespace Langlands.Analytic.AffineAnalytification

open Topology Langlands.AlgebraicGeometry.PointTopology AffinoidAtlasPresentation

/-- Statement (affine case of Conrad–Temkin 2009, Example 2.3.2, as used in Conrad 2011,
printed p.19): for a complete nonarchimedean nontrivially normed field `K` and a finite
polynomial presentation `P` of a commutative `K`-algebra `A`,
1. the map from algebraic `K`-points to `K`-valued points of the constructed atlas is
   bijective;
2. the analytic point map from algebraic `K`-points, with their evaluation topology, to
   the analytification is a topological embedding;
3. algebraic `K`-points are in bijection with `K`-valued points of the saturated atlas,
   compatibly with the analytic point map. -/
def AffineAnalytificationRationalPointsStatement : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (A : Type v) [CommRing A] [Algebra K A] (P : FinitePolynomialPresentation K A),
    Function.Bijective (toFieldPoint K P) ∧
    IsEmbedding (analyticPoint K P) ∧
    ∃ e : AlgPoint K A K ≃ FieldPoint K (saturated K P).presentation,
      ∀ φ, (e φ).point = analyticPoint K P φ

end Langlands.Analytic.AffineAnalytification
