import Langlands.Geometry.Analytic.SpaceAnalytification
import Langlands.Geometry.Analytic.FieldValuedPoints
import Langlands.AlgebraicGeometry.AlgebraicSpace.StructuralAtlasGeometry

/-!
# `K`-valued points of analytifications of separated algebraic spaces

For an analytification of a separated algebraic space locally of finite type, the `K`-valued
points of the analytic space are determined by their underlying points, and they correspond
bijectively to the `K`-points of the algebraic space through `rationalPoint`.
-/

universe u

namespace Langlands.Analytic.SpaceAnalytification

open CategoryTheory SaturatedAtlasPresentation
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.AlgebraicSpace

/-- For a separated algebraic space `X` locally of finite type over `Spec K` and an
analytification `(Y, p)` of `X`:
1. a `K`-valued point of `Y` is determined by its underlying point;
2. for every presentation `P₀` of `K`, there is a bijection from the `K`-points of `X` to the
   `K`-valued points of `Y` sending each `K`-point `x` to a `K`-valued point whose underlying
   point is `rationalPoint p P₀ x`. -/
def SpaceAnalytificationFieldPointsStatement : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (X : AlgebraicSpace (Spec (CommRingCat.of K))),
    IsSeparated X → LocallyOfFiniteTypeOverBase X →
    ∀ (Y : LocalizedCategory.{u, u, u} (K := K)) (p : PointFamily K X Y),
      IsAnalytification K X Y p →
        Function.Injective ((localizedFieldPointProjection K).app Y) ∧
          ∀ P₀ : FinitePolynomialPresentation K K,
            ∃ e : RingPoints K X K ≃ (localizedFieldPointFunctor K).obj Y,
              ∀ x, ULift.down ((localizedFieldPointProjection K).app Y (e x)) =
                rationalPoint p P₀ x

end Langlands.Analytic.SpaceAnalytification
