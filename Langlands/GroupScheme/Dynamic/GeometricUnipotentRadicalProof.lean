import Langlands.GroupScheme.Dynamic.GeometricUnipotentRadicalReduction
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof

/-! # The full geometric radical theorem for dynamic parabolics -/

universe u

namespace Langlands.GroupScheme

/-- The actual identity-limit subgroup of a cocharacter in a connected
reductive group is the full geometric unipotent radical of its dynamic
parabolic, for arbitrary compatible representatives. -/
theorem dynamicGeometricUnipotentRadical :
    DynamicGeometricUnipotentRadicalStatement.{u} :=
  dynamicGeometricUnipotentRadical_of_centralizer dynamicCentralizerReductive

end Langlands.GroupScheme
