import Langlands.Representation.Twist.DualStatement

namespace Langlands

universe uR uG uV

variable {R : Type uR} {G : Type uG} {V : Type uV}
variable [CommRing R] [Group G] [AddCommGroup V] [Module R V]

theorem dual_twist (chi : G →* Rˣ) (rho : Representation R G V) :
    (twist chi rho).dual = twist chi⁻¹ rho.dual := by
  ext g f v
  simp [twist, Representation.dual]

theorem twistDualCompatibility :
    TwistDualCompatibility (R := R) (G := G) (V := V) := by
  intro chi rho
  exact dual_twist chi rho

end Langlands
