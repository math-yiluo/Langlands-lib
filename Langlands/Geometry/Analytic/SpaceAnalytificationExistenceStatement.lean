import Langlands.Geometry.Analytic.SpaceAnalytification
import Langlands.AlgebraicGeometry.AlgebraicSpace.StructuralAtlasGeometry

/-!
# Existence of analytifications of separated algebraic spaces

Every separated algebraic space locally of finite type over a complete nontrivially
valued non-Archimedean field has an analytification in the sense of
`SpaceAnalytification.IsAnalytification`.
-/

universe u

namespace Langlands.Analytic.SpaceAnalytification

open CategoryTheory SaturatedAtlasPresentation
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.AlgebraicSpace

/-- Every separated algebraic space locally of finite type over `Spec K` has an analytic
space in the Library's localized category, with maps from the analytifications of all affine
test points, satisfying `IsAnalytification`. -/
def SpaceAnalytificationExistenceStatement : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (X : AlgebraicSpace (Spec (CommRingCat.of K))),
    IsSeparated X → LocallyOfFiniteTypeOverBase X →
      ∃ (Y : LocalizedCategory.{u, u, u} (K := K)) (p : PointFamily K X Y),
        IsAnalytification K X Y p

end Langlands.Analytic.SpaceAnalytification
