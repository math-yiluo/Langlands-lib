import Langlands.GroupScheme.Dynamic.ConnectedProof
import Langlands.GroupScheme.Rational.RootSignUnipotentLie

/-! # Actual relative-root signs detect dynamic subgroup inclusions -/

universe u

namespace Langlands.GroupScheme

/-- Actual relative-root signs detect dynamic parabolic inclusion and imply
dynamic unipotent inclusion, on every test scheme over an arbitrary field. -/
theorem relativeRootSignInclusions : RelativeRootSignInclusionsStatement.{u} :=
  relativeRootSignInclusions_of_connectedness dynamicConnected

end Langlands.GroupScheme
