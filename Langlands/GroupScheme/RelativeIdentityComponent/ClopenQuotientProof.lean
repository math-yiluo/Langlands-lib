import Langlands.GroupScheme.RelativeIdentityComponent.ClopenQuotientReduction
import Langlands.AlgebraicGeometry.AlgebraicSpace.SeparatedEtaleSchemeProof

/-! # Scheme quotient by a clopen relative identity component -/

universe u

namespace Langlands.GroupScheme.RelativeIdentityComponent

/-- A closed relative identity component of a smooth separated
quasi-compact group has an actual homogeneous quotient scheme. -/
theorem clopenQuotient : ClopenQuotientStatement.{u} :=
  clopenQuotient_of_separatedEtaleScheme
    Langlands.AlgebraicGeometry.AlgebraicSpace.separatedEtaleScheme

end Langlands.GroupScheme.RelativeIdentityComponent
