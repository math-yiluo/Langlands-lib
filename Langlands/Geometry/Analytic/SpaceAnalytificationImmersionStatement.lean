import Langlands.Geometry.Analytic.SpaceAnalytification
import Langlands.AlgebraicGeometry.AlgebraicSpace.StructuralAtlasGeometry
import Langlands.AlgebraicGeometry.AlgebraicSpace.SchemeLocalGeometry

/-!
# Analytification of open and closed immersions of algebraic spaces

The morphism of analytifications induced by an open (closed) immersion of separated
algebraic spaces locally of finite type over `Spec K` is an open (closed) embedding of
underlying topological spaces.
-/

universe u

namespace Langlands.Analytic.SpaceAnalytification

open CategoryTheory Topology SaturatedAtlasPresentation
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.AlgebraicSpace

/-- Let `f : X' ⟶ X` be a morphism of separated algebraic spaces locally of finite type over
`Spec K`, with analytifications `(Y', p')` and `(Y, p)`, and let `F : Y' ⟶ Y` be compatible
with the maps attached to affine test points. Then:
1. if `f` is an open immersion, the underlying map of `F` is an open embedding;
2. if `f` is a closed immersion, the underlying map of `F` is a closed embedding. -/
def SpaceAnalytificationImmersionStatement : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (X' X : AlgebraicSpace (Spec (CommRingCat.of K))) (f : X' ⟶ X),
    IsSeparated X' → LocallyOfFiniteTypeOverBase X' →
    IsSeparated X → LocallyOfFiniteTypeOverBase X →
    ∀ (Y' Y : LocalizedCategory.{u, u, u} (K := K)) (p' : PointFamily K X' Y')
      (p : PointFamily K X Y),
      IsAnalytification K X' Y' p' → IsAnalytification K X Y p →
      ∀ F : Y' ⟶ Y, (∀ (A : Type u) [CommRing A] [Algebra K A]
          (P : FinitePolynomialPresentation K A) (x : RingPoints K X' A),
          p' A P x ≫ F = p A P (RingPoints.map f x)) →
        (Langlands.AlgebraicGeometry.AlgebraicSpace.IsOpenImmersion (hom f) →
          IsOpenEmbedding (localizedSpaceFunctor.map F)) ∧
        (Langlands.AlgebraicGeometry.AlgebraicSpace.IsClosedImmersion (hom f) →
          IsClosedEmbedding (localizedSpaceFunctor.map F))

end Langlands.Analytic.SpaceAnalytification
