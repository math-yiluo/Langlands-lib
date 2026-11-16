import Langlands.Geometry.Analytic.AnalyticImmersion
import Langlands.Geometry.Analytic.SpaceAnalytification
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceMorphismProperties
import Langlands.AlgebraicGeometry.AlgebraicSpace.StructuralAtlasGeometry
import Langlands.AlgebraicGeometry.AlgebraicSpace.SchemeLocalGeometry

/-! # Statement: analytification of algebraic spaces detects open and closed immersions -/

universe u

namespace Langlands.Analytic.SpaceAnalytification

open CategoryTheory SaturatedAtlasPresentation
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.AlgebraicSpace

/-- Let `f : X' ⟶ X` be a morphism of separated algebraic spaces locally of finite type over
`Spec K`, with analytifications `(Y', p')` and `(Y, p)`, and let `F : Y' ⟶ Y` be compatible
with the maps attached to affine test points. Then:
1. `f` is an open immersion if and only if `F` is an open immersion;
2. if `f` is a closed immersion, then `F` is a closed immersion;
3. if `f` is quasi-compact and `F` is a closed immersion, then `f` is a closed immersion. -/
def SpaceAnalytificationAnalyticImmersionStatement : Prop :=
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
        (Langlands.AlgebraicGeometry.AlgebraicSpace.IsOpenImmersion (hom f) ↔
          openImmersion F) ∧
        (Langlands.AlgebraicGeometry.AlgebraicSpace.IsClosedImmersion (hom f) →
          closedImmersion F) ∧
        (IsQuasiCompactMorphism f → closedImmersion F →
          Langlands.AlgebraicGeometry.AlgebraicSpace.IsClosedImmersion (hom f))

end Langlands.Analytic.SpaceAnalytification
