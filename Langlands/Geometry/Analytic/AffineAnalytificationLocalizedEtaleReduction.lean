import Langlands.Geometry.Analytic.FinitePiecesFlatUnramifiedAllPieces
import Langlands.Geometry.Analytic.AffineAnalytificationEtaleStatement
import Langlands.Geometry.Analytic.LocalizedEtaleComposition

/-! # Localized étaleness of analytified étale maps, conditionally

The analytification of an étale map of finitely presented `K`-algebras is étale in the
localized category, given two inputs:

- the published comparison statement `AffineAnalytificationEtaleStatement`, which yields
  the Library's finite-piece formulation `StrongHom.IsEtale` of Berkovich's unramified-and-flat
  condition (Definition 3.3.4);
- the all-pieces comparison `strongEtale_ofSaturation_iff` at original atlas index universe
  `0`, in the direction from all pieces to `strongEtale`.

The upgrade from finite pieces to all pieces in between is proved
(`StrongHom.IsEtale.isEtaleAllPieces`).
-/

noncomputable section

universe u

namespace Langlands.Analytic.AffineAnalytification

open CategoryTheory SaturatedAtlasPresentation

/-- Analytifications of étale algebra maps are étale in the localized category, provided
that (1) `AffineAnalytificationEtaleStatement.{u, u, u}` holds, and (2) for presentations
with original atlas index universe `0` (the profile of `presentation K P`), a strong map
between constructed saturations that is étale over all recognized pieces is `strongEtale`.
Input (2) is the direction `←` of the published `strongEtale_ofSaturation_iff`, which is
stated only when the index universe equals the space universe. -/
def AffineAnalytificationLocalizedEtaleReductionStatement : Prop :=
  AffineAnalytificationEtaleStatement.{u, u, u} →
  (∀ (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
      (X Y : AffinoidAtlasPresentation.{u, u, 0} K) (g : ofSaturation X ⟶ ofSaturation Y),
      AffinoidAtlasPresentation.StrongHom.IsEtaleAllPieces (A := X) (B := Y) g →
        strongEtale g) →
  ∀ (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (A : Type u) [CommRing A] [Algebra K A] (B : Type u) [CommRing B] [Algebra K B]
    (P : FinitePolynomialPresentation K A) (Q : FinitePolynomialPresentation K B)
    (f : A →ₐ[K] B),
    f.toRingHom.Etale → etale (localizedHom K P Q f)

/-- The conditional localized étaleness statement holds: the étale clause of
`AffineAnalytificationEtaleStatement` gives `StrongHom.IsEtale`, the finite-to-all upgrade
gives `IsEtaleAllPieces`, the index-universe comparison gives `strongEtale`, and
`etale_localizationFunctor_map_iff_strongEtale` gives localized étaleness. -/
theorem affineAnalytificationLocalizedEtaleReduction :
    AffineAnalytificationLocalizedEtaleReductionStatement.{u} := by
  intro hAff hComp K _ _ _ A _ _ B _ _ P Q f hf
  have h₁ := (hAff K A B P Q f).2.2.mp hf
  have h₂ := AffinoidAtlasPresentation.StrongHom.IsEtale.isEtaleAllPieces h₁
  exact (etale_localizationFunctor_map_iff_strongEtale (saturatedHom K P Q f)).mpr
    (hComp K (presentation K Q) (presentation K P) (saturatedHom K P Q f) h₂)

end Langlands.Analytic.AffineAnalytification
