import Langlands.BruhatTits.SpecialCompact.AvailableExistencePerLeviReduction
import Langlands.Geometry.Building.BruhatTitsAvailabilityReductionProof
import Langlands.Geometry.Building.GroupAxiomsExistenceReduction
import Langlands.Geometry.Building.RootValuationBuildingConstructionProof
import Langlands.Geometry.Building.RootGroupActionAxiomProof
import Langlands.Geometry.Building.IwahoriDecompositionAxiomProof
import Langlands.Geometry.Building.IntegralModelAxiomsProof

/-! # Existence of a special maximal compact subgroup for available Bruhat–Tits data, with an
assignment for each standard Levi: proof -/

universe u

namespace Langlands.BruhatTits.SpecialCompact

open Langlands.Geometry.Building

/-- **Special maximal compact subgroups for available Bruhat–Tits data** (KP Theorem 4.2.15(1)
at a special vertex; Renard, Théorème V.5.1(2), (3), (5)), with an available assignment for each
actual standard Levi. The one-group clauses of corrected KP Definition 4.1.26 hold for every
connected reductive group (`groupAxiomsExistenceReduction` applied to the four proved focused
statements), so some assignment is valid (`bruhatTitsAvailabilityReduction`), and the
conditional reduction `availableSpecialMaximalCompactExistencePerLevi_of_bruhatTitsAvailability`
gives the target. -/
theorem availableSpecialMaximalCompactExistencePerLevi :
    AvailableSpecialMaximalCompactExistencePerLevi.{u} :=
  availableSpecialMaximalCompactExistencePerLevi_of_bruhatTitsAvailability
    (bruhatTitsAvailabilityReduction
      (groupAxiomsExistenceReduction rootValuationBuildingConstruction rootGroupActionAxiom
        iwahoriDecompositionAxiom integralModelAxioms))

end Langlands.BruhatTits.SpecialCompact
