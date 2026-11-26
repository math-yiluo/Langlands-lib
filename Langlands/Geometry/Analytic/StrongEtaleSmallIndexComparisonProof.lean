import Langlands.Geometry.Analytic.StrongEtaleSmallIndexComparisonStatement
import Langlands.Geometry.Analytic.SaturatedEtaleComparison
import Langlands.Geometry.Analytic.SaturatedAtlasIdempotence
import Langlands.Geometry.Analytic.SaturatedRecognizedPieces

/-! # Proof: étale recognition for small-index affine analytic presentations -/

universe u v w

namespace Langlands.Analytic.SaturatedAtlasPresentation

open _root_.CategoryTheory AffinoidAtlasPresentation

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- For original presentations in any index universe, the canonical strong
étale property of a strong map between the constructed saturations agrees with
étaleness over all recognized pieces of the original presentations. -/
theorem strongEtale_ofSaturation_iff_isEtaleAllPieces
    {P Q : AffinoidAtlasPresentation.{u, v, w} K} (f : ofSaturation P ⟶ ofSaturation Q) :
    strongEtale f ↔ StrongHom.IsEtaleAllPieces (A := P) (B := Q) f := by
  have key : ∀ (S T : SaturatedAtlasPresentation.{u, v, v} K),
      S = ofSaturation P → T = ofSaturation Q →
      (∀ g : S ⟶ T, strongEtale g ↔ IsEtaleOnRecognizedPieces g) →
      ∀ g : ofSaturation P ⟶ ofSaturation Q,
        strongEtale g ↔ IsEtaleOnRecognizedPieces g := by
    rintro S T rfl rfl h
    exact h
  refine (key (ofSaturation P.saturatedPresentation) (ofSaturation Q.saturatedPresentation)
    (ofSaturation_saturatedPresentation P) (ofSaturation_saturatedPresentation Q) ?_ f).trans
      (StrongHom.isEtaleAllPieces_iff_isEtaleOnRecognizedPieces f).symm
  intro g
  exact (strongEtale_ofSaturation_iff g).trans
    (StrongHom.isEtaleAllPieces_iff_isEtaleOnRecognizedPieces g)

/-- Small-index all-pieces recognition: for original atlas index universe `0`
and ambient space universe equal to that of the field, a strong map between
constructed saturations that is étale on all recognized pieces is strong
étale. -/
theorem strongEtaleSmallIndexComparison : StrongEtaleSmallIndexComparisonStatement.{u} := by
  intro K _ _ _ P Q f hf
  exact (strongEtale_ofSaturation_iff_isEtaleAllPieces f).mpr hf

end Langlands.Analytic.SaturatedAtlasPresentation
