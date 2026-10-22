import Langlands.Representation.Twist.Definitions
import Mathlib.Algebra.Group.Hom.Instances

namespace Langlands

universe uR uG uV

variable {R : Type uR} {G : Type uG} {V : Type uV}
variable [CommRing R] [Group G] [AddCommGroup V] [Module R V]

/-- The unit, multiplication, and inverse laws for scalar twisting. -/
def TwistAlgebraLaws : Prop :=
  ∀ (chi eta : G →* Rˣ) (rho : Representation R G V),
    twist 1 rho = rho ∧
    twist chi (twist eta rho) = twist (chi * eta) rho ∧
    twist chi⁻¹ (twist chi rho) = rho ∧
    twist chi (twist chi⁻¹ rho) = rho

end Langlands
