import Langlands.Geometry.Building.KPLocalMoyPrasadGroupPropertiesReduction
import Langlands.Geometry.Building.KPQuasiSplitLocalTorusFiltrationProof

/-! # Group properties of the K-level Moy–Prasad groups

The published torus-filtration theorem supplies the last input of the
conjugation, commutator and intersection assembly.
-/

universe u

namespace Langlands.Geometry.Building.MaximalUnramified

/-- All eight group properties of the published K-level Moy–Prasad groups. -/
theorem localMoyPrasadGroupProperties : LocalMoyPrasadGroupPropertiesStatement.{u} :=
  localMoyPrasadGroupProperties_of_torus_filtration quasiSplitLocalTorusFiltration

end Langlands.Geometry.Building.MaximalUnramified
