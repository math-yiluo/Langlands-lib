import Langlands.Representation.Twist.Definitions

namespace Langlands

universe uR uG uH uV

variable {R : Type uR} {G : Type uG} {H : Type uH} {V : Type uV}
variable [CommRing R] [Group G] [Group H] [AddCommGroup V] [Module R V]

/-- Twisting commutes with restriction along a group homomorphism. -/
def TwistPullbackCompatibility : Prop :=
  ∀ (chi : G →* Rˣ) (rho : Representation R G V) (phi : H →* G),
    (twist chi rho).comp phi = twist (chi.comp phi) (rho.comp phi)

end Langlands
