import Langlands.BruhatTits.SpecialCompact.JointBasisStatement
import Langlands.Representation.Exponents.MaximalLeviSupercuspidalReducibilityStatement

/-! # Renard VII.1.3 from a joint compact basis -/

universe u v

namespace Langlands.Aubert.General.RepresentedParabolic

/-- The joint Cartan and compact-open basis implies the full represented
maximal-Levi reducibility criterion. -/
def MaximalLeviReducibilityFromJointBasisStatement : Prop :=
  BruhatTits.SpecialCompact.JointSpecialCompactBasisExistenceStatement.{u} →
  MaximalLeviSupercuspidalReducibilityStatement.{u, v}

end Langlands.Aubert.General.RepresentedParabolic
