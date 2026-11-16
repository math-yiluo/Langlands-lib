import Langlands.Geometry.Building.RankOneCorootReduction
import Langlands.Geometry.Building.QuasiSplitValuedRankOneCoordinatesProof

/-! # The local coroot component formula over the maximal unramified field -/

universe u

namespace Langlands.Geometry.Building

/-- The centralizer component of an opposite-root commutator is the image of a
point of an induced torus satisfying the required geometric-character bound. -/
theorem kpLocalCorootComponent : KPLocalCorootComponentStatement.{u} := by
  intro F _ _ _ _ H _ B hZ a
  exact inducedCorootComponentProperty_of_valuedRankOneCoordinates
    (quasiSplitValuedRankOneCoordinates F H B hZ) a

end Langlands.Geometry.Building
