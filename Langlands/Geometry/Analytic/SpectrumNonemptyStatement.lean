import Langlands.Geometry.Analytic.Affinoid

/-! # Nonemptiness of a nonzero strict affinoid spectrum -/

universe u

namespace Langlands.Analytic.PresentedStrictAffinoidAlgebra

variable (K : Type u) [NormedField K] [IsUltrametricDist K]

/-- Every nonzero presented strict affinoid algebra has an actual bounded
multiplicative seminorm. The scalar valuation may be trivial. -/
def SpectrumNonemptyStatement [CompleteSpace K] : Prop :=
  ∀ (P : PresentedStrictAffinoidAlgebra K), Nontrivial P → Nonempty (BanachSpectrum P)

end Langlands.Analytic.PresentedStrictAffinoidAlgebra
