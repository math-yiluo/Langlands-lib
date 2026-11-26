import Langlands.HarmonicAnalysis.Basic
import Langlands.LocalField.ResidueNormalization

/-! # Scalar change of variables for local-field Haar integrals -/

open MeasureTheory

namespace Langlands.HarmonicAnalysis

universe u

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- Scaling the argument of a Schwartz–Bruhat function by a nonzero scalar
multiplies its additive Haar integral by the inverse normalized absolute value. -/
def LocalFieldScalarHaarIntegralStatement : Prop :=
  ∀ [MeasurableSpace F] [BorelSpace F] (μ : Measure F) [μ.IsAddHaarMeasure]
    (a : Fˣ) (f : SchwartzBruhat F),
    (∫ x, f ((a : F) * x) ∂μ) =
      (LocalField.residueNormalizedAbsoluteValue F (a : F))⁻¹ • (∫ x, f x ∂μ)

end Langlands.HarmonicAnalysis
