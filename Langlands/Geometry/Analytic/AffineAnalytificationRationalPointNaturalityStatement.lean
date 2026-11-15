import Langlands.Geometry.Analytic.AffineAnalytificationRationalPoints
import Langlands.Geometry.Analytic.AffineAnalytificationMap

/-! # Statement: naturality of the analytic points of algebraic rational points -/

universe u v w

namespace Langlands.Analytic.AffineAnalytification

open Langlands.AlgebraicGeometry.PointTopology

/-- Statement (affine case of the functoriality of the identification `X(K) = X^an(K)`,
Conrad–Temkin 2009, Example 2.3.2 and Theorem 2.2.3, as used in Conrad 2011, printed
p.19): for a complete nonarchimedean nontrivially normed field `K`, finite polynomial
presentations `P` of `A` and `Q` of `B`, a `K`-algebra map `f : A → B` and an algebraic
`K`-point `φ` of `B`, the analytification map induced by `f` sends the analytic point of
`φ` to the analytic point of `φ ∘ f`. -/
def AffineAnalytificationRationalPointNaturalityStatement : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (A : Type v) [CommRing A] [Algebra K A] (B : Type w) [CommRing B] [Algebra K B]
    (P : FinitePolynomialPresentation K A) (Q : FinitePolynomialPresentation K B)
    (f : A →ₐ[K] B) (φ : AlgPoint K B K),
    baseMap K P Q f (analyticPoint K Q φ) = analyticPoint K P (AlgPoint.precomp f φ)

end Langlands.Analytic.AffineAnalytification
