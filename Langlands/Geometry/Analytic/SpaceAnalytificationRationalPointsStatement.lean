import Langlands.Geometry.Analytic.SpaceAnalytification
import Langlands.AlgebraicGeometry.AlgebraicSpace.StructuralAtlasGeometry
import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleChartTopology

/-!
# Rational points of analytifications of separated algebraic spaces

The underlying space of an analytification of a separated algebraic space locally of finite
type is Hausdorff, and the map from `K`-points to analytic points is a topological embedding
for the étale-chart topology on `X(K)`.
-/

universe u

namespace Langlands.Analytic.SpaceAnalytification

open CategoryTheory SaturatedAtlasPresentation Topology
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.AlgebraicSpace

/-- For a separated algebraic space `X` locally of finite type over `Spec K` and an
analytification `(Y, p)` of `X`, the underlying space of `Y` is Hausdorff and, for every
presentation `P₀` of `K`, the map `rationalPoint p P₀ : X(K) → Y` is a topological embedding
when `X(K)` carries the étale-chart topology. -/
def SpaceAnalytificationRationalPointsStatement : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (X : AlgebraicSpace (Spec (CommRingCat.of K))),
    IsSeparated X → LocallyOfFiniteTypeOverBase X →
    ∀ (Y : LocalizedCategory.{u, u, u} (K := K)) (p : PointFamily K X Y),
      IsAnalytification K X Y p →
        T2Space (localizedSpaceFunctor.obj Y) ∧
          ∀ P₀ : FinitePolynomialPresentation K K,
            @IsEmbedding _ _ (etaleChartTopology K X) _ (rationalPoint p P₀)

end Langlands.Analytic.SpaceAnalytification
