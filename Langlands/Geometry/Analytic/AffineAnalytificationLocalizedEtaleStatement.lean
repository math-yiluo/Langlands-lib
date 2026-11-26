import Langlands.Geometry.Analytic.AffineAnalytificationLocalizedMap
import Langlands.Geometry.Analytic.EtaleSite

/-! # Analytifications of étale algebra maps are étale -/

universe u v w

namespace Langlands.Analytic.AffineAnalytification

/-- The analytification `Spec(B)ᵃⁿ → Spec(A)ᵃⁿ` of an étale map of `K`-algebras with finite
polynomial presentations is étale in the Library's localized category (Berkovich 1990,
Proposition 3.4.6(3), one direction, affine case). -/
def AffineAnalytificationLocalizedEtaleStatement : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (A : Type v) [CommRing A] [Algebra K A] (B : Type w) [CommRing B] [Algebra K B]
    (P : FinitePolynomialPresentation K A) (Q : FinitePolynomialPresentation K B)
    (f : A →ₐ[K] B),
    f.toRingHom.Etale → SaturatedAtlasPresentation.etale (localizedHom K P Q f)

end Langlands.Analytic.AffineAnalytification
