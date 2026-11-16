import Langlands.BruhatTits.SpecialCompact.AvailableExistencePerLeviStatement
import Langlands.BruhatTits.SpecialCompact.AvailableExistenceReduction

/-! # The per-Levi existence target from Bruhat–Tits availability -/

noncomputable section

universe u

namespace Langlands.BruhatTits.SpecialCompact

open Langlands.Geometry.Building

/-- `BruhatTitsAvailabilityStatement` implies `AvailableSpecialMaximalCompactExistencePerLevi`. -/
theorem availableSpecialMaximalCompactExistencePerLevi_of_bruhatTitsAvailability
    (hAvail : BruhatTitsAvailabilityStatement.{u}) :
    AvailableSpecialMaximalCompactExistencePerLevi.{u} :=
  fun F _ _ _ _ G hG S i hi ν =>
    availableSpecialMaximalCompact_perLevi_of_bruhatTitsAvailability hAvail F G hG S i hi ν

set_option linter.defProp false in
/-- Record entry: the conditional implication from Bruhat–Tits availability to the
per-Levi special maximal compact existence target. -/
def availableSpecialMaximalCompactExistencePerLeviOfBruhatTitsAvailability :
    BruhatTitsAvailabilityStatement.{u} → AvailableSpecialMaximalCompactExistencePerLevi.{u} :=
  availableSpecialMaximalCompactExistencePerLevi_of_bruhatTitsAvailability

end Langlands.BruhatTits.SpecialCompact
