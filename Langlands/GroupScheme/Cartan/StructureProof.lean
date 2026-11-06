import Langlands.GroupScheme.Cartan.StructureReduction
import Langlands.GroupScheme.Torus.FiniteFieldGeometricAssembly
import Langlands.GroupScheme.Absolute.MaximalTorusConjugacyProof

/-! # Smooth connected nilpotent structure of Cartan subgroups -/

universe u

namespace Langlands.GroupScheme

/-- Every Cartan subgroup of a smooth connected affine group over any field is
smooth, connected, and geometrically nilpotent. -/
theorem cartanStructure : CartanStructureStatement.{u} :=
  cartanStructure_of_finiteFieldGeometricMaximalTorus
    (finiteFieldGeometricMaximalTorus_of_maximalTorusConjugacy maximalTorusConjugacy)

end Langlands.GroupScheme
