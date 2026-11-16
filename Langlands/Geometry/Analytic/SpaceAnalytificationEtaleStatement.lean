import Langlands.Geometry.Analytic.SpaceAnalytification
import Langlands.AlgebraicGeometry.AlgebraicSpace.StructuralAtlasGeometry
import Langlands.AlgebraicGeometry.AlgebraicSpace.HenselianSpacePointTopologyStatement

/-!
# Analytification of algebraic spaces detects étale morphisms

A morphism of separated algebraic spaces locally of finite type over `Spec K` is étale
exactly when the induced morphism of analytifications is étale.
-/

universe u

namespace Langlands.Analytic.SpaceAnalytification

open CategoryTheory SaturatedAtlasPresentation
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.AlgebraicSpace

/-- Let `f : X' ⟶ X` be a morphism of separated algebraic spaces locally of finite type over
`Spec K`, with analytifications `(Y', p')` and `(Y, p)`. A morphism `F : Y' ⟶ Y` compatible
with the maps attached to affine test points is étale exactly when `f` is étale. -/
def SpaceAnalytificationEtaleStatement : Prop :=
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
        (IsEtaleMorphism f ↔ SaturatedAtlasPresentation.etale F)

end Langlands.Analytic.SpaceAnalytification
