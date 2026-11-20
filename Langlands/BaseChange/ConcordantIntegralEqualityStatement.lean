import Langlands.BaseChange.RegularTransferStatement

/-! # Integrals of concordant test functions -/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory Langlands.HarmonicAnalysis Langlands.QuotientIntegration

attribute [local instance high] leftQuotientMeasurableSpace
attribute [local instance] leftQuotient_borelSpace

/-- The constant-weight consequence of the two Weyl integration formulas in
Henniart–Lemaire 2011, II.2.10. For the Haar measures used in concordance, the
integrals of two concordant test functions agree. -/
def ConcordantIntegralEqualityStatement.{u, v} : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F]
    (E : Type v) [CommRing E] [Algebra F E] [TopologicalSpace E] [IsTopologicalRing E]
    [IsModuleTopology F E] (σ : E ≃ₐ[F] E) (l n : ℕ), IsCyclicAlgebra σ l →
    ∀ [MeasurableSpace (GeneralLinear n F)] [BorelSpace (GeneralLinear n F)]
      [MeasurableSpace (GeneralLinear n E)] [BorelSpace (GeneralLinear n E)]
      (μF : Measure (GeneralLinear n F)) [μF.IsHaarMeasure]
      (μE : Measure (GeneralLinear n E)) [μE.IsHaarMeasure]
      (φ : SchwartzBruhat (GeneralLinear n E)) (f : SchwartzBruhat (GeneralLinear n F)),
      AreConcordant σ l μF μE φ f → (∫ δ, φ δ ∂μE) = ∫ γ, f γ ∂μF

end Langlands.BaseChange
