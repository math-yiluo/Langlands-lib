import Langlands.Geometry.Building.BruhatTitsAvailabilityStatement
import Langlands.Representation.Exponents.ArbitraryParabolicCasselmanStatement

/-! # Casselman's criterion from Bruhat–Tits availability -/

universe u v

namespace Langlands.Aubert.General.RepresentedParabolic

/-- A valid corrected Bruhat–Tits assignment gives the corrected criterion
for all represented rational parabolics. -/
def CasselmanFromBuildingStatement : Prop :=
  Geometry.Building.BruhatTitsAvailabilityStatement.{u} →
    ArbitraryParabolicCasselmanCriterionStatement.{u, v}

end Langlands.Aubert.General.RepresentedParabolic
