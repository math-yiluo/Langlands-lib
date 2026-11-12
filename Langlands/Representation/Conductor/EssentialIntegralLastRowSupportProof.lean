import Langlands.Representation.Conductor.EssentialIntegralLastRowSupportStatement
import Langlands.Representation.Conductor.EssentialIntegralSupportSeries
import Langlands.Representation.Conductor.IntegralLastRowSupportReduction

noncomputable section

namespace Langlands.Conductor

universe uF uV

/-- Integral last-row support of the corrected essential vector, over every
nonarchimedean local field and with independent carrier universes. -/
theorem essentialIntegralLastRowSupport :
    EssentialIntegralLastRowSupportStatement.{uF, uV} := by
  intro F _ _ _ _ n _ _ _ _ _ _ _ _ q ψ abv ϖ μ h V _ _ π hπ ℓ _hℓ w hw g hW j
  obtain ⟨⟨P, hP, hid⟩, hrest⟩ := hw
  exact integral_last_row_of_polynomial_degreeCoefficients
    h π hπ.2.1.1 ℓ w hrest
    (fun d => degreeCorankOneModelCoefficient_eq_polynomial_of_essentialIdentity
      h π hπ.2.1.1 ℓ w P hP.1 hid d) g hW j

end Langlands.Conductor
