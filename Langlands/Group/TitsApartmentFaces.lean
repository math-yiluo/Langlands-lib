import Langlands.Group.TitsBorelChambers

/-! # Faces and chambers in restricted Tits apartments -/

namespace Langlands.Group

open TitsSystem RelativeWeyl

variable {G W : Type*} [Group G] [Group W]
  {B N : Subgroup G} {π : N →* W} {S : Set W}

namespace IsTitsSystem

variable (h : IsTitsSystem B N π S)
include h

/-- Conjugation preserves admissible parabolics. -/
theorem isAdmissibleParabolic_conjugate {Q : Subgroup G}
    (hQ : IsAdmissibleParabolic B π S Q) (a : G) :
    IsAdmissibleParabolic B π S (conjugateSubgroup a Q) := by
  obtain ⟨g, X, hX, hQ⟩ := hQ
  have hQ' : Q = conjugateSubgroup g (h.standardParabolicSubgroup hX.1) :=
    SetLike.coe_injective hQ
  refine ⟨a * g, X, hX, ?_⟩
  rw [hQ', ← conjugateSubgroup_mul]
  exact h.coe_conjugate_standardParabolic hX.1 _

/-- An admissible parabolic containing `B` is standard of an admissible type. -/
theorem exists_admissible_standardParabolic_eq {Q : Subgroup G}
    (hQ : IsAdmissibleParabolic B π S Q) (hBQ : B ≤ Q) :
    ∃ (X : Set W) (hX : IsAdmissibleType S X),
      Q = h.standardParabolicSubgroup hX.1 := by
  obtain ⟨g, X, hX, hQ⟩ := hQ
  have hQ' : Q = conjugateSubgroup g (h.standardParabolicSubgroup hX.1) :=
    SetLike.coe_injective hQ
  have hg : g ∈ Q := h.mem_of_eq_conjugate hBQ (h.le_of_coe_eq rfl) hQ'
  have heq := congrArg (conjugateSubgroup g⁻¹) hQ'
  rw [conjugateSubgroup_eq_self (Q.inv_mem hg), ← conjugateSubgroup_mul,
    inv_mul_cancel, conjugateSubgroup_one] at heq
  exact ⟨X, hX, heq⟩

/-- An admissible overgroup of an apartment parabolic is in the same apartment. -/
theorem mem_restrictedApartment_of_le {a : G} {P Q : Subgroup G}
    (hP : P ∈ restrictedApartment B π S a)
    (hQ : IsAdmissibleParabolic B π S Q) (hPQ : P ≤ Q) :
    Q ∈ restrictedApartment B π S a := by
  obtain ⟨n, X, hX, hP⟩ := h.mem_restrictedApartment_iff_conjugate.mp hP
  let t : G := a * n
  have hBQ : conjugateSubgroup t B ≤ Q := by
    rw [hP] at hPQ
    exact (Subgroup.map_mono (h.le_of_coe_eq rfl)).trans hPQ
  have hB : B ≤ conjugateSubgroup t⁻¹ Q := by
    have H := Subgroup.map_mono (f := (MulAut.conj t⁻¹).toMonoidHom) hBQ
    change conjugateSubgroup t⁻¹ (conjugateSubgroup t B) ≤
      conjugateSubgroup t⁻¹ Q at H
    simpa only [← conjugateSubgroup_mul, inv_mul_cancel, conjugateSubgroup_one] using H
  obtain ⟨Y, hY, heq⟩ := h.exists_admissible_standardParabolic_eq
    (h.isAdmissibleParabolic_conjugate hQ t⁻¹) hB
  refine h.mem_restrictedApartment_iff_conjugate.mpr ⟨n, Y, hY, ?_⟩
  calc
    Q = conjugateSubgroup t (conjugateSubgroup t⁻¹ Q) := by
      rw [← conjugateSubgroup_mul, mul_inv_cancel, conjugateSubgroup_one]
    _ = conjugateSubgroup t (h.standardParabolicSubgroup hY.1) := by rw [heq]

/-- Each apartment parabolic contains a Borel conjugate from that apartment. -/
theorem exists_conjugate_borel_le_in_restrictedApartment {a : G} {P : Subgroup G}
    (hP : P ∈ restrictedApartment B π S a) :
    ∃ n : N, conjugateSubgroup (a * n) B ∈ restrictedApartment B π S a ∧
      conjugateSubgroup (a * n) B ≤ P := by
  obtain ⟨n, X, hX, hP⟩ := h.mem_restrictedApartment_iff_conjugate.mp hP
  have hempty : h.standardParabolicSubgroup (Set.empty_subset S) = B :=
    SetLike.coe_injective h.standardParabolic_empty
  refine ⟨n, h.mem_restrictedApartment_iff_conjugate.mpr
    ⟨n, ∅, isAdmissibleType_empty S, ?_⟩, ?_⟩
  · rw [hempty]
  · rw [hP]
    exact Subgroup.map_mono (h.le_of_coe_eq rfl)

/-- Choose the normalizer element giving a contained Borel in this apartment. -/
noncomputable def restrictedApartmentBorelRepresentative {a : G} {P : Subgroup G}
    (hP : P ∈ restrictedApartment B π S a) : N :=
  (h.exists_conjugate_borel_le_in_restrictedApartment hP).choose

theorem restrictedApartmentBorelRepresentative_spec {a : G} {P : Subgroup G}
    (hP : P ∈ restrictedApartment B π S a) :
    conjugateSubgroup (a * h.restrictedApartmentBorelRepresentative hP) B ∈
        restrictedApartment B π S a ∧
      conjugateSubgroup (a * h.restrictedApartmentBorelRepresentative hP) B ≤ P :=
  (h.exists_conjugate_borel_le_in_restrictedApartment hP).choose_spec

end IsTitsSystem
end Langlands.Group
