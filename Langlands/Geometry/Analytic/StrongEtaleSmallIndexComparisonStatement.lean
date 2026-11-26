import Langlands.Geometry.Analytic.AffineAnalytificationLocalizedEtaleReduction

/-! # Étale recognition for small-index affine analytic presentations -/

universe u

namespace Langlands.Analytic.SaturatedAtlasPresentation

open _root_.CategoryTheory AffinoidAtlasPresentation

/-- The small-index case of all-pieces étale recognition. Analytic affine
polynomial-locus presentations have ambient universe `u` and chart-index universe `0`. -/
def StrongEtaleSmallIndexComparisonStatement : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (P Q : AffinoidAtlasPresentation.{u, u, 0} K) (f : ofSaturation P ⟶ ofSaturation Q),
    StrongHom.IsEtaleAllPieces (A := P) (B := Q) f → strongEtale f

end Langlands.Analytic.SaturatedAtlasPresentation
