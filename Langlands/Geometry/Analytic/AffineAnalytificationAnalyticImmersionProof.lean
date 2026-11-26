import Langlands.Geometry.Analytic.AffineAnalytificationAnalyticImmersionStatement
import Langlands.Geometry.Analytic.AffineAnalytificationClosedImmersionPreservation
import Langlands.Geometry.Analytic.AffineAnalytificationClosedImmersionReflection
import Langlands.Geometry.Analytic.AffineAnalytificationOpenImmersionPreservation
import Langlands.Geometry.Analytic.AffineAnalytificationOpenImmersionReflection

/-! # Affine analytification detects open and closed immersions -/

universe u v

namespace Langlands.Analytic.AffineAnalytification

/-- A map of finitely presented algebras is surjective exactly when its affine
analytification is an analytic closed immersion, and its spectrum map is an open
immersion exactly when its affine analytification is an analytic open immersion. -/
theorem affineAnalytificationAnalyticImmersion :
    AffineAnalytificationAnalyticImmersionStatement.{u, v} := by
  intro K _ _ _ A B _ _ _ _ P Q f
  exact ⟨⟨fun hf => closedImmersion_localizedHom_of_surjective K P f hf Q,
      surjective_of_closedImmersion_localizedHom P Q f⟩,
    ⟨openImmersion_localizedHom_of_isOpenImmersion P Q f,
      isOpenImmersion_of_openImmersion_localizedHom P Q f⟩⟩

end Langlands.Analytic.AffineAnalytification
