import Langlands.Geometry.Analytic.AffineAnalytificationEtaleProof
import Langlands.Geometry.Analytic.AffineAnalytificationLocalizedEtaleStatement
import Langlands.Geometry.Analytic.LocalizedEtaleComposition
import Langlands.Geometry.Analytic.StrongEtaleSmallIndexComparisonProof

/-! # Analytifications of étale algebra maps are étale in the localized category -/

universe u v w

namespace Langlands.Analytic.AffineAnalytification

open SaturatedAtlasPresentation

/-- The analytification `Spec(B)ᵃⁿ → Spec(A)ᵃⁿ` of an étale map of `K`-algebras with finite
polynomial presentations is étale in the localized category (Berkovich 1990,
Proposition 3.4.6(3), one direction, affine case). -/
theorem affineAnalytificationLocalizedEtale :
    AffineAnalytificationLocalizedEtaleStatement.{u, v, w} := by
  intro K _ _ _ A _ _ B _ _ P Q f hf
  exact (etale_localizationFunctor_map_iff_strongEtale (saturatedHom K P Q f)).mpr
    ((strongEtale_ofSaturation_iff_isEtaleAllPieces (saturatedHom K P Q f)).mpr
      ((affineAnalytificationEtale K A B P Q f).2.2.mp hf).isEtaleAllPieces)

end Langlands.Analytic.AffineAnalytification
