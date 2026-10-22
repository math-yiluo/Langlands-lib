import Langlands.Representation.Twist.Definitions

namespace Langlands

universe uR uG uV

variable {R : Type uR} {G : Type uG} {V : Type uV}
variable [CommRing R] [Group G] [AddCommGroup V] [Module R V]

/-- The algebraic dual of a twist has the inverse character twist. -/
def TwistDualCompatibility : Prop :=
  ∀ (chi : G →* Rˣ) (rho : Representation R G V),
    (twist chi rho).dual = twist chi⁻¹ rho.dual

end Langlands
