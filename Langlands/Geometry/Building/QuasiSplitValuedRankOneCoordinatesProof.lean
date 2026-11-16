import Langlands.Geometry.Building.AlgebraicRankOneCoordinatesExistenceProof
import Langlands.Geometry.Building.ValuedRankOneCoordinateSpecialization
import Langlands.Geometry.Building.QuasiSplitValuedRankOneCoordinatesStatement

/-! # Existence of coherent valued rank-one coordinates -/

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.LocalGalois.Separable

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Geometry.Building

/-- Every indivisible relative root of the supplied building data has coherent valued
SL2 or SU3 coordinates over the maximal unramified field. -/
theorem quasiSplitValuedRankOneCoordinates :
    QuasiSplitValuedRankOneCoordinatesStatement.{u} := by
  intro F _ _ _ _ H _ B hZ b hb
  have hcoords := algebraicRankOneCoordinatesExistence (UnramifiedClosure F) H
    B.isConnectedReductive B.S (B.centralizerTorus hZ)
    B.i B.centralizer.j B.centralizer.s
    B.isMaximalSplitTorus hZ B.centralizer.isRepresentedBy B.centralizer.comp_eq b hb
  constructor
  · intro h2b
    obtain ⟨C, hn⟩ := hcoords.1 h2b
    exact ⟨ValuedSL2RootCoordinates.ofAlgebraic B hZ C hb.1 hn⟩
  · intro h2b
    obtain ⟨C, hn⟩ := hcoords.2 h2b
    exact ⟨ValuedSU3RootCoordinates.ofAlgebraic B hZ C hb.1 h2b hn⟩

end Langlands.Geometry.Building
