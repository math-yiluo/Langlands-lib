import Langlands.Geometry.Analytic.SpaceAnalytification

/-!
# Analytic quotients of étale affine chart families of separated algebraic spaces

A family of étale affine test points of a separated algebraic space over `Spec K` has an
analytic quotient in the Library's localized category: an analytic space receiving étale,
jointly surjective maps from the chart analytifications, under which every affine fibre
square of two charts becomes a pullback square (Conrad–Temkin, Theorem 4.2.2).
-/

universe u

namespace Langlands.Analytic.SpaceAnalytification

open CategoryTheory SaturatedAtlasPresentation
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.AlgebraicSpace
open Langlands.AlgebraicGeometry.PointTopology (ringTestMap)

/-- For every family of étale affine test points `xᵢ : Spec Aᵢ → X` of a separated algebraic
space `X` over `Spec K`, there are an analytic space `Y` and maps `πᵢ : Spec(Aᵢ)ᵃⁿ → Y` in the
Library's localized category such that every `πᵢ` is étale, the `πᵢ` are jointly surjective on
underlying points, and every fibre square of presheaves `Spec B = Spec Aᵢ ×_X Spec Aⱼ` of
affine test points is carried to a pullback square. -/
def SpaceAnalytificationChartQuotientStatement : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (X : AlgebraicSpace (Spec (CommRingCat.of K))), IsSeparated X →
    ∀ (ι : Type u) (A : ι → Type u) [∀ i, CommRing (A i)] [∀ i, Algebra K (A i)]
      (P : ∀ i, FinitePolynomialPresentation K (A i)) (x : ∀ i, RingPoints K X (A i)),
      (∀ i, AlgebraicSpace.IsEtale (pointHom K (x i))) →
      ∃ (Y : LocalizedCategory.{u, u, u} (K := K))
        (π : ∀ i, AffineAnalytification.localized K (P i) ⟶ Y),
        (∀ i, SaturatedAtlasPresentation.etale (π i)) ∧
        (∀ y : localizedSpaceFunctor.obj Y,
          ∃ i, y ∈ Set.range (localizedSpaceFunctor.map (π i))) ∧
        ∀ (i j : ι) {B : Type u} [CommRing B] [Algebra K B]
          (Q : FinitePolynomialPresentation K B) (f : A i →ₐ[K] B) (g : A j →ₐ[K] B),
          IsPullback ((schemeYoneda (Spec (CommRingCat.of K))).map (ringTestMap K f))
              ((schemeYoneda (Spec (CommRingCat.of K))).map (ringTestMap K g))
              (pointHom K (x i)) (pointHom K (x j)) →
            IsPullback (AffineAnalytification.localizedHom K (P i) Q f)
              (AffineAnalytification.localizedHom K (P j) Q g) (π i) (π j)

end Langlands.Analytic.SpaceAnalytification
