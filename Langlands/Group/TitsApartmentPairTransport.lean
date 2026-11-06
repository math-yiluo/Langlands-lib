import Langlands.Group.TitsApartmentComparison

/-! # Comparison between two arbitrary restricted apartments -/

namespace Langlands.Group

open TitsSystem RelativeWeyl

variable {G W : Type*} [Group G] [Group W]
  {B N : Subgroup G} {π : N →* W} {S : Set W}

namespace IsTitsSystem

variable (h : IsTitsSystem B N π S)
include h

/-- Two facets in a common restricted apartment admit a transporter to any
other apartment containing them, belonging to both facet parabolics. -/
theorem exists_mem_intersection_restrictedApartment_transport
    (a g : G) {P Q : Subgroup G}
    (hPa : P ∈ restrictedApartment B π S a)
    (hQa : Q ∈ restrictedApartment B π S a)
    (hPg : P ∈ restrictedApartment B π S g)
    (hQg : Q ∈ restrictedApartment B π S g) :
    ∃ k : G, k ∈ P ∧ k ∈ Q ∧
      conjugateSubgroup k '' restrictedApartment B π S a =
        restrictedApartment B π S g := by
  obtain ⟨n₀, X, hX, hP⟩ := h.mem_restrictedApartment_iff_conjugate.mp hPa
  let t : G := a * n₀
  have hAt : restrictedApartment B π S t = restrictedApartment B π S a :=
    h.restrictedApartment_mul_normalizer a n₀
  rw [← hAt] at hQa
  obtain ⟨n, Y, hY, hQ⟩ := h.mem_restrictedApartment_iff_conjugate.mp hQa
  have hP' : h.standardParabolicSubgroup hX.1 ∈
      restrictedApartment B π S (t⁻¹ * g) := by
    rw [← h.image_conjugateSubgroup_restrictedApartment t⁻¹ g]
    refine ⟨P, hPg, ?_⟩
    rw [hP, ← conjugateSubgroup_mul]
    simp [t]
  have hQ' : conjugateSubgroup (n : G) (h.standardParabolicSubgroup hY.1) ∈
      restrictedApartment B π S (t⁻¹ * g) := by
    rw [← h.image_conjugateSubgroup_restrictedApartment t⁻¹ g]
    refine ⟨Q, hQg, ?_⟩
    rw [hQ, ← conjugateSubgroup_mul]
    simp
  obtain ⟨k, hkP, hkQ, hkA⟩ :=
    h.exists_mem_two_parabolics_restrictedApartment_eq
      (h.le_of_coe_eq rfl) (h.le_of_coe_eq rfl) n (t⁻¹ * g) hP' hQ'
  refine ⟨t * k * t⁻¹, ?_, ?_, ?_⟩
  · rw [hP]
    exact ⟨k, hkP, rfl⟩
  · rw [hQ, conjugateSubgroup_mul]
    exact ⟨k, hkQ, rfl⟩
  · rw [← hAt, h.image_conjugateSubgroup_restrictedApartment]
    have heq : (t * k * t⁻¹) * t = t * k := by simp [mul_assoc]
    rw [heq, ← h.image_conjugateSubgroup_restrictedApartment, hkA,
      h.image_conjugateSubgroup_restrictedApartment]
    simp

/-- A chosen two-facet transporter between arbitrary restricted apartments. -/
noncomputable def restrictedApartmentPairTransport
    (a g : G) {P Q : Subgroup G}
    (hPa : P ∈ restrictedApartment B π S a)
    (hQa : Q ∈ restrictedApartment B π S a)
    (hPg : P ∈ restrictedApartment B π S g)
    (hQg : Q ∈ restrictedApartment B π S g) : ↥(P ⊓ Q) :=
  ⟨(h.exists_mem_intersection_restrictedApartment_transport a g hPa hQa hPg hQg).choose,
    (h.exists_mem_intersection_restrictedApartment_transport a g hPa hQa hPg hQg).choose_spec.1,
    (h.exists_mem_intersection_restrictedApartment_transport a g hPa hQa hPg hQg).choose_spec.2.1⟩

/-- The chosen transporter carries the entire first apartment to the second. -/
theorem image_restrictedApartmentPairTransport
    (a g : G) {P Q : Subgroup G}
    (hPa : P ∈ restrictedApartment B π S a)
    (hQa : Q ∈ restrictedApartment B π S a)
    (hPg : P ∈ restrictedApartment B π S g)
    (hQg : Q ∈ restrictedApartment B π S g) :
    conjugateSubgroup
        (h.restrictedApartmentPairTransport a g hPa hQa hPg hQg : G) ''
      restrictedApartment B π S a = restrictedApartment B π S g :=
  (h.exists_mem_intersection_restrictedApartment_transport a g hPa hQa hPg hQg).choose_spec.2.2

/-- The transporter fixes each overgroup of either shared facet parabolic. -/
theorem restrictedApartmentPairTransport_conjugate_eq_self
    (a g : G) {P Q : Subgroup G}
    (hPa : P ∈ restrictedApartment B π S a)
    (hQa : Q ∈ restrictedApartment B π S a)
    (hPg : P ∈ restrictedApartment B π S g)
    (hQg : Q ∈ restrictedApartment B π S g)
    {R : Subgroup G} (hR : P ≤ R ∨ Q ≤ R) :
    conjugateSubgroup
      (h.restrictedApartmentPairTransport a g hPa hQa hPg hQg : G) R = R := by
  apply conjugateSubgroup_eq_self
  rcases hR with hR | hR
  · exact hR (h.restrictedApartmentPairTransport a g hPa hQa hPg hQg).property.1
  · exact hR (h.restrictedApartmentPairTransport a g hPa hQa hPg hQg).property.2

end IsTitsSystem

end Langlands.Group
