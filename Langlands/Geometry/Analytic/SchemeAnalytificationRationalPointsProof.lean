import Langlands.Geometry.Analytic.SchemeAnalytificationRationalPointsReduction
import Langlands.Geometry.Analytic.AffineAnalytificationRationalPointNaturalityProof
import Langlands.Geometry.Analytic.AffineAnalytificationRationalPointsProof
import Langlands.Geometry.Analytic.SchemeAnalytificationOpenGluing

/-! # Rational points of the glued scheme analytification -/

universe u

namespace Langlands.Analytic.SchemeAnalytification

open CategoryTheory _root_.AlgebraicGeometry Topology
open Langlands.AlgebraicGeometry.PointTopology

/-- Actual rational points embed into the glued analytification, independently of
the affine chart used to compute them. -/
theorem schemeAnalytificationRationalPoints :
    SchemeAnalytificationRationalPointsStatement.{u} := by
  intro K _ _ _ X f _
  let : TopologicalSpace (RingPoint K (Over.mk f) K) :=
    schemePointTopology K (Over.mk f) K
  have hnat :=
    AffineAnalytification.affineAnalytificationRationalPointNaturality.{u, u, u}
  have haff (A : Type u) [CommRing A] [Algebra K A]
      (P : FinitePolynomialPresentation K A) :
      IsEmbedding (AffineAnalytification.analyticPoint K P) :=
    (AffineAnalytification.affineAnalytificationRationalPoints K A P).2.1
  have he := RationalPointsComparison.isEmbedding_analyticRationalPoint
    K f hnat haff (OpenGluing.isOpenEmbedding_ι K f)
  exact ⟨RationalPointsComparison.chart_independence K f hnat, he.injective,
    RationalPointsComparison.range_analyticRationalPoint K f hnat, he⟩

end Langlands.Analytic.SchemeAnalytification
