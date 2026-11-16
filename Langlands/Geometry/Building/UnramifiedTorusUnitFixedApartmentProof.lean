import Langlands.Geometry.Building.UnramifiedTorusUnitFixedApartmentReduction
import Langlands.Geometry.Building.UnramifiedFixedPointTransporterProof
import Langlands.Geometry.Building.UnramifiedTwistedFixedTranslationProof
import Langlands.Geometry.Building.UnramifiedSplitTranslationFixerProof

/-! # The torus-unit-fixed coefficient-fixed locus lies in the fixed special apartment -/

universe u

namespace Langlands.Geometry.Building

/-- **KP Proposition 9.3.13 over `K`, with the corrected split-translation argument.**
Every coefficient-fixed building point fixed by the full split-torus unit kernel
is the image of a coefficient-fixed point of the special apartment. -/
theorem unramifiedTorusUnitFixedApartment :
    UnramifiedTorusUnitFixedApartmentStatement.{u} :=
  unramifiedTorusUnitFixedApartmentReduction
    unramifiedFixedPointTransporter.{u}
    unramifiedTwistedFixedTranslation.{u}
    unramifiedSplitTranslationFixer.{u}

end Langlands.Geometry.Building
