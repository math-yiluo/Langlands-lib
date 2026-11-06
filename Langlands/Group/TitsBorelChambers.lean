import Langlands.Group.TitsApartmentComparison

/-! # Minimal admissible parabolics in a Tits system -/

namespace Langlands.Group

open TitsSystem RelativeWeyl

variable {G W : Type*} [Group G] [Group W]
  {B N : Subgroup G} {π : N →* W} {S : Set W}

namespace TitsSystem

/-- The empty type is admissible, including when the generating set is empty. -/
theorem isAdmissibleType_empty (S : Set W) : IsAdmissibleType S ∅ :=
  ⟨Set.empty_subset _, fun s hs => ⟨s, hs, Relation.ReflTransGen.refl, by simp⟩⟩

end TitsSystem

namespace IsTitsSystem

variable (h : IsTitsSystem B N π S)
include h

/-- Conjugates of the distinguished Borel are admissible parabolics. -/
theorem isAdmissibleParabolic_conjugate_borel (g : G) :
    IsAdmissibleParabolic B π S (conjugateSubgroup g B) := by
  refine ⟨g, ∅, isAdmissibleType_empty S, ?_⟩
  unfold conjStandardParabolic
  rw [h.standardParabolic_empty]
  rfl

/-- Forward Borel transporters into an overgroup of the Borel are its elements. -/
theorem conjugate_borel_le_iff {P : Subgroup G} (hBP : B ≤ P) (g : G) :
    conjugateSubgroup g B ≤ P ↔ g ∈ P := by
  constructor
  · intro hle
    apply P.inv_mem_iff.mp
    apply h.mem_of_conjugate_le hBP g⁻¹
    intro b hb
    apply hle
    exact ⟨b, hb, by simp⟩
  · intro hg
    rintro _ ⟨b, hb, rfl⟩
    exact P.mul_mem (P.mul_mem hg (hBP hb)) (P.inv_mem hg)

/-- Inclusion between two Borel conjugates is equality. -/
theorem conjugate_borel_eq_of_le (g k : G)
    (hle : conjugateSubgroup g B ≤ conjugateSubgroup k B) :
    conjugateSubgroup g B = conjugateSubgroup k B := by
  have hle' : conjugateSubgroup (k⁻¹ * g) B ≤ B := by
    have H := Subgroup.map_mono (f := (MulAut.conj k⁻¹).toMonoidHom) hle
    change conjugateSubgroup k⁻¹ (conjugateSubgroup g B) ≤
      conjugateSubgroup k⁻¹ (conjugateSubgroup k B) at H
    simpa only [← conjugateSubgroup_mul, inv_mul_cancel, conjugateSubgroup_one] using H
  have hmem : k⁻¹ * g ∈ B := (h.conjugate_borel_le_iff le_rfl _).mp hle'
  calc
    conjugateSubgroup g B = conjugateSubgroup k (conjugateSubgroup (k⁻¹ * g) B) := by
      rw [← conjugateSubgroup_mul]
      simp
    _ = conjugateSubgroup k B := by rw [conjugateSubgroup_eq_self hmem]

/-- An admissible parabolic contained in a Borel conjugate equals it. -/
theorem eq_conjugate_borel_of_isAdmissible_of_le {P : Subgroup G}
    (hP : IsAdmissibleParabolic B π S P) (g : G)
    (hle : P ≤ conjugateSubgroup g B) : P = conjugateSubgroup g B := by
  obtain ⟨k, X, hX, hP⟩ := hP
  have hP' : P = conjugateSubgroup k (h.standardParabolicSubgroup hX.1) :=
    SetLike.coe_injective hP
  have hBP : conjugateSubgroup k B ≤ P := by
    rw [hP']
    exact Subgroup.map_mono (h.le_of_coe_eq rfl)
  have heq := h.conjugate_borel_eq_of_le k g (hBP.trans hle)
  exact le_antisymm hle (heq ▸ hBP)

end IsTitsSystem
end Langlands.Group
