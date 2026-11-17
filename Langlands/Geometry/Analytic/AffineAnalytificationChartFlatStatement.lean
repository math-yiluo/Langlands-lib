import Langlands.Geometry.Analytic.AffineAnalytificationAtlas
import Mathlib.RingTheory.RingHom.Flat

/-! # Statement: the chart algebras of the affine analytification are flat -/

universe u v

namespace Langlands.Analytic.AffineAnalytification

/-- Statement (Berkovich 1990, last paragraph of the proof of Theorem 3.4.1, for the
Library's polynomial-locus charts): for a complete nonarchimedean nontrivially normed
field `K`, a commutative `K`-algebra `A` with a finite polynomial presentation `P`, and
every chart index `m`, the algebra map from `A` to the `m`-th chart algebra (the
affinoid algebra of the closed polydisc of radius `radius K m` in the analytification)
is flat. -/
def AffineAnalytificationChartFlatStatement : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (A : Type v) [CommRing A] [Algebra K A] (P : FinitePolynomialPresentation K A)
    (m : ℕ),
    (PolynomialLocus.algebraMap P (AnalyticAffineSpace.polyradius K P.arity m)).toRingHom.Flat

end Langlands.Analytic.AffineAnalytification
