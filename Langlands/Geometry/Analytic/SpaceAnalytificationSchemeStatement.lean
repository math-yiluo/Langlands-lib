import Langlands.Geometry.Analytic.SpaceAnalytification
import Langlands.Geometry.Analytic.SchemeAnalytificationRationalPoints
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Analytifications of schemes as algebraic spaces

For a separated scheme `X` locally of finite type over `K`, the underlying space of any
analytification of the algebraic space of `X` is the glued analytification space of `X`,
compatibly with the affine open charts and with rational points.
-/

universe u

namespace Langlands.Analytic.SpaceAnalytification

open CategoryTheory SaturatedAtlasPresentation
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.AlgebraicSpace
open Langlands.Analytic.AffineSchemeAnalytification Langlands.Analytic.SchemeAnalytification

/-- Let `X` be a separated scheme locally of finite type over `K`, with structure morphism
`f`, and let `(Y, p)` be an analytification of the algebraic space of `X`. There is a
homeomorphism `e` from the underlying space of `Y` to the glued analytification space
`Space K f` such that:
1. for every affine open `U` of `X` and the test point of `X` given by the inclusion
   `Spec Γ(U) ≅ U ⟶ X`, the map attached by `p` to this point, followed by `e`, is the
   canonical map `ι K f U` from the analytification of `U`;
2. for every `K`-point `x` of `X`, `e` sends the analytic point `rationalPoint p P₀ x` to
   the point `analyticRationalPoint K f x` of the glued space. -/
def SpaceAnalytificationSchemeStatement : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType f]
    [_root_.AlgebraicGeometry.IsSeparated f]
    (Y : LocalizedCategory.{u, u, u} (K := K))
    (p : PointFamily K ((schemeToSpace _).obj (Over.mk f)) Y),
    IsAnalytification K ((schemeToSpace _).obj (Over.mk f)) Y p →
    ∃ e : localizedSpaceFunctor.obj Y ≃ₜ Space K f,
      (∀ (U : X.affineOpens)
        (x : RingPoints K ((schemeToSpace _).obj (Over.mk f))
          (CoordinateRing (structureMap f U))),
        (schemeRingPointsEquiv K (Over.mk f) _ x).left =
            (coordinateIso (structureMap f U)).inv ≫ (U : X.Opens).ι →
          ∀ y : LocalSpace K f U,
            e (localizedSpaceFunctor.map (p _ (chartPresentation K f U) x) y) =
              ι K f U y) ∧
      ∀ (P₀ : FinitePolynomialPresentation K K)
        (x : RingPoints K ((schemeToSpace _).obj (Over.mk f)) K),
        e (rationalPoint p P₀ x) = analyticRationalPoint K f (schemeRingPointsEquiv K _ K x)

end Langlands.Analytic.SpaceAnalytification
