import Langlands.Geometry.Analytic.Spectrum.Definitions
import Mathlib.Analysis.Normed.Field.Ultra

/-! # Strong triangle inequality for multiplicative seminorms -/

universe u v

namespace Langlands.Analytic

/-- A natural-number bound forces a multiplicative seminorm to be
nonarchimedean; spectrum seminorms over an ultrametric field satisfy it. -/
def SpectrumNonarchimedeanStatement : Prop :=
  (∀ (A : Type u) [CommRing A] (p : MulRingSeminorm A),
    (∀ n : ℕ, p (n : A) ≤ 1) → IsNonarchimedean p) ∧
  (∀ (A : Type u) (K : Type v) [NormedCommRing A] [NormedField K]
    [IsUltrametricDist K] [NormedAlgebra K A] (x : BanachSpectrum A),
    IsNonarchimedean x.toMulRingSeminorm)

end Langlands.Analytic
