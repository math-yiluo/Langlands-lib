import Langlands.Group.TitsApartmentPanels
import Langlands.Group.TitsSystemExchange

/-! # Parabolic subgroups below admissible parabolics -/

namespace Langlands.Group

open TitsSystem RelativeWeyl

variable {G W : Type*} [Group G] [Group W]
  {B N : Subgroup G} {π : N →* W} {S : Set W}

namespace IsTitsSystem

variable (h : IsTitsSystem B N π S)
include h

/-- A subgroup containing `B` and contained in an admissible parabolic has
an admissible standard type. -/
theorem exists_admissible_standardParabolic_eq_of_le {P Q : Subgroup G}
    (hBP : B ≤ P) (hQ : IsAdmissibleParabolic B π S Q) (hPQ : P ≤ Q) :
    ∃ (X : Set W) (hX : IsAdmissibleType S X),
      P = h.standardParabolicSubgroup hX.1 := by
  obtain ⟨Y, hY, hQeq⟩ :=
    h.exists_admissible_standardParabolic_eq hQ (hBP.trans hPQ)
  obtain ⟨X, hXS, hPeq⟩ := h.exists_eq_standardParabolic P hBP
  have hPeq' : P = h.standardParabolicSubgroup hXS :=
    SetLike.coe_injective hPeq
  have hXY : X ⊆ Y := (h.standardParabolicSubgroup_le_iff hXS hY.1).mp
    (by simpa only [← hPeq', ← hQeq] using hPQ)
  exact ⟨X, hY.mono hXY, hPeq'⟩

/-- Admissibility passes to a parabolic subgroup contained in an admissible
parabolic subgroup. -/
theorem isAdmissibleParabolic_of_le {P Q : Subgroup G}
    (hP : IsParabolic B P) (hQ : IsAdmissibleParabolic B π S Q) (hPQ : P ≤ Q) :
    IsAdmissibleParabolic B π S P := by
  obtain ⟨g, hg⟩ := hP
  have hBP : B ≤ conjugateSubgroup g⁻¹ P := by
    have H := Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hg
    change conjugateSubgroup g⁻¹ (conjugateSubgroup g B) ≤
      conjugateSubgroup g⁻¹ P at H
    simpa only [← conjugateSubgroup_mul, inv_mul_cancel, conjugateSubgroup_one] using H
  obtain ⟨X, hX, heq⟩ := h.exists_admissible_standardParabolic_eq_of_le hBP
    (h.isAdmissibleParabolic_conjugate hQ g⁻¹)
    (Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hPQ)
  have hP' : IsAdmissibleParabolic B π S (conjugateSubgroup g⁻¹ P) := by
    refine ⟨1, X, hX, ?_⟩
    rw [heq]
    simpa only [conjugateSubgroup_one] using h.coe_conjugate_standardParabolic hX.1 1
  simpa only [← conjugateSubgroup_mul, mul_inv_cancel, conjugateSubgroup_one] using
    h.isAdmissibleParabolic_conjugate hP' g

/-- Choose an admissible standard type for a subgroup between `B` and an
admissible parabolic, retaining its equality with the standard subgroup. -/
noncomputable def admissibleStandardTypeOfLE {P Q : Subgroup G}
    (hBP : B ≤ P) (hQ : IsAdmissibleParabolic B π S Q) (hPQ : P ≤ Q) :
    { X : { X : Set W // IsAdmissibleType S X } //
      P = h.standardParabolicSubgroup X.2.1 } := by
  classical
  let ht := h.exists_admissible_standardParabolic_eq_of_le hBP hQ hPQ
  exact ⟨⟨ht.choose, ht.choose_spec.choose⟩, ht.choose_spec.choose_spec⟩

end IsTitsSystem
end Langlands.Group
