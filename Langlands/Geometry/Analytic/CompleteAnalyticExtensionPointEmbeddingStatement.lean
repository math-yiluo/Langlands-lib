import Langlands.Geometry.Analytic.SpaceAnalytificationGroundFieldStatement
import Langlands.AlgebraicGeometry.AlgebraicSpace.ExtensionPointMap

/-! # The analytification comparison for extension of rational points -/

universe u

namespace Langlands.Analytic.SpaceAnalytification

open CategoryTheory SaturatedAtlasPresentation Topology
open AffinoidAtlasPresentation.GroundFieldExtension (localizedFunctor localizedProjection)
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.AlgebraicSpace

/-- With the analytic ground-field comparison, the algebraic embedding of rational
points over complete nonarchimedean fields is identified by the analytic projection and
has closed image for the étale-chart topologies. -/
def CompleteAnalyticExtensionPointEmbeddingStatement : Prop :=
  SpaceAnalytificationGroundFieldStatement.{u} →
  ∀ (K L : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L] [NormedAlgebra K L]
    (X : AlgebraicSpace (Spec (CommRingCat.of K))),
    IsSeparated X → LocallyOfFiniteTypeOverBase X →
    ∀ (Y : LocalizedCategory.{u, u, u} (K := K)) (p : PointFamily K X Y),
      IsAnalytification K X Y p →
      let XL := baseChange (Spec.algebraMap K L) X
      let F := localizedFunctor.{u, u, u, u} K L
      ∃ q : PointFamily L XL (F.obj Y),
        IsAnalytification L XL (F.obj Y) q ∧
        (∀ (P : FinitePolynomialPresentation K K) (Q : FinitePolynomialPresentation L L)
          (x : RingPoints K X K),
          ((localizedProjection K L).app Y
            (ULift.up (rationalPoint q Q (extensionPointMap L X x)))).down =
              rationalPoint p P x) ∧
        @IsClosedEmbedding _ _ (etaleChartTopology K X) (etaleChartTopology L XL)
          (extensionPointMap L X)

end Langlands.Analytic.SpaceAnalytification
