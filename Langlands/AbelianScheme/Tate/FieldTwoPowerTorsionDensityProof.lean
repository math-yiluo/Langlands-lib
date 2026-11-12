import Langlands.AbelianScheme.Tate.FieldTwoPowerTorsionDensityStatement
import Langlands.AbelianScheme.Tate.TwoPowerTorsionDensityReduction
import Langlands.AbelianScheme.FieldCubePullbackProof
import Langlands.AbelianScheme.AlgebraicallyClosedFieldAmpleExistenceProof

/-! # Density of actual geometric two-power torsion

Discharge both antecedents of the published reduction
`fieldTwoPowerTorsionDensity_reduction` by the published balanced cube pullback
identity and ample existence over algebraically closed fields.
-/

universe u

namespace Langlands.AbelianScheme.Tate

/-- Two-power torsion is Zariski dense in every abelian variety over an
algebraically closed characteristic-zero field. -/
theorem fieldTwoPowerTorsionDensity : FieldTwoPowerTorsionDensityStatement.{u} :=
  fieldTwoPowerTorsionDensity_reduction GroupScheme.fieldCubePullback.{u}
    GroupScheme.algebraicallyClosedFieldAmpleExistence.{u}

end Langlands.AbelianScheme.Tate
