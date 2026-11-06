import Langlands.Group.TitsApartmentComparison

/-! # Common restricted apartments for two admissible parabolics -/

namespace Langlands.Group

open TitsSystem RelativeWeyl

variable {G W : Type*} [Group G] [Group W]
  {B N : Subgroup G} {π : N →* W} {S : Set W}

namespace IsTitsSystem

variable (h : IsTitsSystem B N π S)
include h

/-- Any two admissible parabolics belong to a common restricted apartment. -/
theorem exists_common_restrictedApartment {P Q : Subgroup G}
    (hP : IsAdmissibleParabolic B π S P) (hQ : IsAdmissibleParabolic B π S Q) :
    ∃ a : G, P ∈ restrictedApartment B π S a ∧ Q ∈ restrictedApartment B π S a := by
  obtain ⟨g, X, hX, hP⟩ := hP
  obtain ⟨k, Y, hY, hQ⟩ := hQ
  have hP' : P = conjugateSubgroup g (h.standardParabolicSubgroup hX.1) :=
    SetLike.coe_injective hP
  have hQ' : Q = conjugateSubgroup k (h.standardParabolicSubgroup hY.1) :=
    SetLike.coe_injective hQ
  obtain ⟨w, n, hn, b, hb, c, hc, hrel⟩ := h.exists_mem_cell (g⁻¹ * k)
  have hk : k = (g * b * n) * c := by
    calc
      k = g * (g⁻¹ * k) := by simp
      _ = (g * b * n) * c := by rw [hrel]; simp only [mul_assoc]
  have hbX : b ∈ h.standardParabolicSubgroup hX.1 := (h.le_of_coe_eq rfl) hb
  have hcY : c ∈ h.standardParabolicSubgroup hY.1 := (h.le_of_coe_eq rfl) hc
  refine ⟨g * b, h.mem_restrictedApartment_iff_conjugate.mpr ⟨1, X, hX, ?_⟩,
    h.mem_restrictedApartment_iff_conjugate.mpr ⟨n, Y, hY, ?_⟩⟩
  · simpa only [Subgroup.coe_one, mul_one, conjugateSubgroup_mul,
      conjugateSubgroup_eq_self hbX] using hP'
  · rw [hQ', hk, conjugateSubgroup_mul, conjugateSubgroup_eq_self hcY]

/-- A chosen representative of a restricted apartment containing both parabolics. -/
noncomputable def commonRestrictedApartmentRepresentative {P Q : Subgroup G}
    (hP : IsAdmissibleParabolic B π S P) (hQ : IsAdmissibleParabolic B π S Q) : G :=
  (h.exists_common_restrictedApartment hP hQ).choose

theorem mem_commonRestrictedApartment_left {P Q : Subgroup G}
    (hP : IsAdmissibleParabolic B π S P) (hQ : IsAdmissibleParabolic B π S Q) :
    P ∈ restrictedApartment B π S (h.commonRestrictedApartmentRepresentative hP hQ) :=
  (h.exists_common_restrictedApartment hP hQ).choose_spec.1

theorem mem_commonRestrictedApartment_right {P Q : Subgroup G}
    (hP : IsAdmissibleParabolic B π S P) (hQ : IsAdmissibleParabolic B π S Q) :
    Q ∈ restrictedApartment B π S (h.commonRestrictedApartmentRepresentative hP hQ) :=
  (h.exists_common_restrictedApartment hP hQ).choose_spec.2

end IsTitsSystem
end Langlands.Group
