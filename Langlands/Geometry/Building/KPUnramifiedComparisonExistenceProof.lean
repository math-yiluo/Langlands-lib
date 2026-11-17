import Langlands.Geometry.Building.KPUnramifiedComparisonFieldStatements
import Langlands.Geometry.Building.SpecialTorusExistenceProof
import Langlands.Geometry.Building.UnramifiedValuationDescentProof
import Langlands.Geometry.Building.KPUnramifiedComparisonRootFieldProof
import Langlands.Geometry.Building.KPUnramifiedComparisonLeviFieldProof
import Langlands.Geometry.Building.KPUnramifiedComparisonZeroFieldProof
import Langlands.Geometry.Building.KPUnramifiedComparisonOpenProof

/-! # Existence of the unramified comparison of building data -/

universe u

namespace Langlands.Geometry.Building

/-- The special-torus apartment lift and its proved comparison fields give
the comparison with the maximal unramified extension, at arbitrary universe. -/
theorem unramifiedComparisonExistence :
    UnramifiedComparisonExistenceStatement.{u} :=
  unramifiedComparisonExistence_of_fields
    specialTorusExistence unramifiedValuationDescent
    unramifiedComparisonRootField unramifiedComparisonLeviField
    unramifiedComparisonZeroField unramifiedComparisonOpenField

end Langlands.Geometry.Building
