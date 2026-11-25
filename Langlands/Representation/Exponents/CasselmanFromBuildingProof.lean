import Langlands.Representation.Exponents.CasselmanFromBuildingStatement
import Langlands.Representation.Exponents.CasselmanNecessity
import Langlands.Representation.Exponents.CasselmanSufficiencyReduction
import Langlands.BruhatTits.SpecialCompact.JointBasisFinalAssembly
import Langlands.BruhatTits.SpecialCompact.AvailableBasisProof

/-! # Assembly of the corrected Casselman criterion from a valid building assignment -/

universe u v

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme BruhatTits.SpecialCompact

/-- Bruhat–Tits availability supplies the simultaneous Cartan and compact basis
data used in sufficiency. Necessity is already unconditional. -/
theorem casselmanFromBuilding : CasselmanFromBuildingStatement.{u, v} := by
  intro hBuilding
  have hBasis := jointSpecialCompactBasisExistence_of_availability_and_basis
    hBuilding availableSimultaneousStandardBasis
  have hSufficiency :=
    arbitraryParabolicCasselmanSufficiency_of_jointSpecialCompactBasis.{u, v} hBasis
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  have := hG.smooth
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ _ _ haar _ π hπ hc
  exact ⟨arbitraryParabolicCasselmanNecessity k G hG haar π, hSufficiency k G hG haar π hπ hc⟩

end Langlands.Aubert.General.RepresentedParabolic
