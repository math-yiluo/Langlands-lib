import Langlands.Geometry.Analytic.SpaceAnalytification
import Langlands.AlgebraicGeometry.AlgebraicSpace.StructuralAtlasGeometry

/-!
# Morphisms of analytifications of algebraic spaces

A morphism `f : X' ⟶ X` of algebraic spaces over `Spec K`, with `X'` separated and locally
of finite type, induces a unique morphism between given analytifications that is compatible
with the maps attached to affine test points.
-/

universe u

namespace Langlands.Analytic.SpaceAnalytification

open CategoryTheory SaturatedAtlasPresentation
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.AlgebraicSpace

/-- For `f : X' ⟶ X` with `X'` separated and locally of finite type over `Spec K`, and
analytifications `(Y', p')` of `X'` and `(Y, p)` of `X`, there is exactly one morphism
`F : Y' ⟶ Y` with `p' A P x ≫ F = p A P (f x)` for every affine test point `x` of `X'`. -/
def SpaceAnalytificationMorphismStatement : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (X' X : AlgebraicSpace (Spec (CommRingCat.of K))) (f : X' ⟶ X),
    IsSeparated X' → LocallyOfFiniteTypeOverBase X' →
    ∀ (Y' Y : LocalizedCategory.{u, u, u} (K := K)) (p' : PointFamily K X' Y')
      (p : PointFamily K X Y),
      IsAnalytification K X' Y' p' → IsAnalytification K X Y p →
        ∃! F : Y' ⟶ Y, ∀ (A : Type u) [CommRing A] [Algebra K A]
          (P : FinitePolynomialPresentation K A) (x : RingPoints K X' A),
          p' A P x ≫ F = p A P (RingPoints.map f x)

end Langlands.Analytic.SpaceAnalytification
