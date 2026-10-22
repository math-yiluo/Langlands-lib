import Langlands.Representation.Twist.PullbackStatement

namespace Langlands

universe uR uG uH uV

variable {R : Type uR} {G : Type uG} {H : Type uH} {V : Type uV}
variable [CommRing R] [Group G] [Group H] [AddCommGroup V] [Module R V]

theorem twist_comp (chi : G →* Rˣ) (rho : Representation R G V) (phi : H →* G) :
    (twist chi rho).comp phi = twist (chi.comp phi) (rho.comp phi) := by
  ext g v
  rfl

theorem twistPullbackCompatibility :
    TwistPullbackCompatibility (R := R) (G := G) (H := H) (V := V) := by
  intro chi rho phi
  exact twist_comp chi rho phi

end Langlands
