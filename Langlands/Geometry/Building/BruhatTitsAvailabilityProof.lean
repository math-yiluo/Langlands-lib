import Langlands.Geometry.Building.BruhatTitsAvailabilityReductionProof
import Langlands.Geometry.Building.GroupAxiomsExistenceProof

/-! # Bruhat–Tits availability over nonarchimedean local fields -/

universe u

namespace Langlands.Geometry.Building

/-- There is an assignment of building data to connected reductive groups over nonarchimedean
local fields in universe `u` that satisfies all ten axioms of corrected KP Definition 4.1.26. -/
theorem bruhatTitsAvailability : BruhatTitsAvailabilityStatement.{u} :=
  bruhatTitsAvailabilityReduction groupAxiomsExistence

end Langlands.Geometry.Building
