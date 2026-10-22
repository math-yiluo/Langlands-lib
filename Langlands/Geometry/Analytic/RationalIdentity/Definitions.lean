import Langlands.Geometry.Analytic.RationalLocalization.Definitions

/-! # Actual fractions for an invertible rational denominator -/

noncomputable section

universe u

namespace Langlands.Analytic.RationalIdentity

/-- Fractions in the original algebra, formed using the inverse of an actual unit. -/
def fractions (K : Type u) [NormedField K] [IsUltrametricDist K]
    (P : PresentedStrictAffinoidAlgebra K) (m : ℕ) (g : Pˣ) (f : Fin m → P) :
    Fin m → P := fun i => (↑g⁻¹ : P) * f i

end Langlands.Analytic.RationalIdentity
