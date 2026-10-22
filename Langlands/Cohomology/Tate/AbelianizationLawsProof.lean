import Langlands.Cohomology.Tate.AbelianizationStatement
import Langlands.Cohomology.Tate.AbelianizationRestriction

universe u

namespace Langlands.Tate

/-- The actual degree-minus-two maps induce inclusion and group transfer. -/
theorem abelianizationLaws : AbelianizationLaws.{u} := by
  intro G _ _ H _ _
  exact ⟨integralMinusTwoEquiv_corestriction H, integralMinusTwoEquiv_restriction H⟩

end Langlands.Tate
