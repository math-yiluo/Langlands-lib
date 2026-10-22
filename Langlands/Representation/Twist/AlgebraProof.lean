import Langlands.Representation.Twist.AlgebraStatement

namespace Langlands

universe uR uG uV

variable {R : Type uR} {G : Type uG} {V : Type uV}
variable [CommRing R] [Group G] [AddCommGroup V] [Module R V]

@[simp]
theorem twist_one (rho : Representation R G V) : twist 1 rho = rho := by
  ext g v
  simp [twist]

theorem twist_twist (chi eta : G →* Rˣ) (rho : Representation R G V) :
    twist chi (twist eta rho) = twist (chi * eta) rho := by
  ext g v
  simp [twist, smul_smul]

@[simp]
theorem twist_inv_twist (chi : G →* Rˣ) (rho : Representation R G V) :
    twist chi⁻¹ (twist chi rho) = rho := by
  ext g v
  simp [twist, smul_smul]

@[simp]
theorem twist_twist_inv (chi : G →* Rˣ) (rho : Representation R G V) :
    twist chi (twist chi⁻¹ rho) = rho := by
  ext g v
  simp [twist, smul_smul]

/-- The complete bundled target, without extra hypotheses. -/
theorem twistAlgebraLaws : TwistAlgebraLaws (R := R) (G := G) (V := V) := by
  intro chi eta rho
  exact ⟨twist_one rho, twist_twist chi eta rho,
    twist_inv_twist chi rho, twist_twist_inv chi rho⟩

end Langlands
