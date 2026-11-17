import Langlands.Geometry.Building.KPUnramifiedMoyPrasadComparison
import Langlands.Geometry.Building.KPLocalMoyPrasadGroupPropertiesProof
import Langlands.Geometry.Building.KPUnramifiedComparisonExistenceProof

/-! # The rational Moy–Prasad family from the maximal unramified extension -/

universe u

namespace Langlands.Geometry.Building

/-- The inverse images of the actual K-level Moy–Prasad groups form a rational
Moy–Prasad family over F, at arbitrary universe. -/
theorem unramifiedRationalMoyPrasad : UnramifiedRationalMoyPrasadStatement.{u} :=
  unramifiedRationalMoyPrasad_of_unramifiedComparison
    MaximalUnramified.localMoyPrasadGroupProperties unramifiedComparisonExistence

end Langlands.Geometry.Building
