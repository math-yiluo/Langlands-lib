import Langlands.Geometry.Analytic.SchemeAnalytificationRationalPoints

/-! # Statement: rational points of the glued analytification of a scheme -/

universe u

namespace Langlands.Analytic.SchemeAnalytification

open CategoryTheory _root_.AlgebraicGeometry Topology
open Langlands.AlgebraicGeometry.PointTopology

/-- Statement (scheme case of Conrad–Temkin 2009, Example 2.3.2, as used in Conrad 2011,
printed p.19, and of Berkovich 1990, Theorem 3.4.1(i), for `K`-points): for a complete
nonarchimedean nontrivially normed field `K` and a scheme `X` locally of finite type over
`Spec K`,
1. the analytic point of a `K`-point does not depend on the affine open through which it
   is computed;
2. the map from actual `K`-points to the glued analytification is injective;
3. its image is the union of the images of the `K`-points of all affine analytifications;
4. it is a topological embedding for the published affine-chart topology on `X(K)`. -/
def SchemeAnalytificationRationalPointsStatement : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType f],
    (∀ (U : X.affineOpens) (q : RingPoint K (openOver K (Over.mk f) U.val) K),
      analyticRationalPoint K f (openPointMap K (Over.mk f) K U.val q) =
        ι K f U (localAnalyticPoint K f U q)) ∧
    Function.Injective (analyticRationalPoint K f) ∧
    Set.range (analyticRationalPoint K f) =
      (⋃ U : X.affineOpens,
        ι K f U '' Set.range (AffineAnalytification.analyticPoint K (chartPresentation K f U))) ∧
    @IsEmbedding _ _ (schemePointTopology K (Over.mk f) K) _ (analyticRationalPoint K f)

end Langlands.Analytic.SchemeAnalytification
