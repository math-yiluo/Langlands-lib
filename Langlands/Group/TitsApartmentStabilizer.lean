import Langlands.Group.TitsBorelThickness

/-! # The stabilizer of the standard restricted apartment -/

namespace Langlands.Group

open TitsSystem RelativeWeyl

variable {G W : Type*} [Group G] [Group W]
  {B N : Subgroup G} {π : N →* W} {S : Set W}

namespace IsTitsSystem

variable (h : IsTitsSystem B N π S)
include h

theorem standardParabolicSubgroup_empty :
    h.standardParabolicSubgroup (Set.empty_subset S) = B :=
  SetLike.coe_injective h.standardParabolic_empty

/-- Each restricted apartment contains the Borel conjugates of its chambers. -/
theorem conjugate_borel_mem_restrictedApartment (a : G) (n : N) :
    conjugateSubgroup (a * n) B ∈ restrictedApartment B π S a :=
  h.mem_restrictedApartment_iff_conjugate.mpr
    ⟨n, ∅, isAdmissibleType_empty S, by rw [h.standardParabolicSubgroup_empty]⟩

theorem borel_mem_restrictedApartment_one : B ∈ restrictedApartment B π S 1 := by
  simpa using h.conjugate_borel_mem_restrictedApartment 1 1

/-- If `B` belongs to the apartment based at `a`, then `a n ∈ B` for some
`n ∈ N`. -/
theorem exists_mul_mem_of_borel_mem {a : G} (hB : B ∈ restrictedApartment B π S a) :
    ∃ n : N, a * n ∈ B := by
  obtain ⟨n, X, hX, hBX⟩ := h.mem_restrictedApartment_iff_conjugate.mp hB
  refine ⟨n, (h.conjugate_borel_le_iff le_rfl (a * n)).mp ?_⟩
  calc conjugateSubgroup (a * n) B
      ≤ conjugateSubgroup (a * n) (h.standardParabolicSubgroup hX.1) :=
        Subgroup.map_mono (h.le_of_coe_eq rfl)
    _ = B := hBX.symm

/-- An element `b ∈ B` whose apartment contains the chamber `m B m⁻¹` of the
standard apartment lies in `m B m⁻¹`. -/
theorem mem_conjugate_borel_of_mem {b : G} (hb : b ∈ B) {m : N}
    (hm : conjugateSubgroup (m : G) B ∈ restrictedApartment B π S b) :
    b ∈ conjugateSubgroup (m : G) B := by
  obtain ⟨n, X, hX, hmX⟩ := h.mem_restrictedApartment_iff_conjugate.mp hm
  have hle : conjugateSubgroup (b * n) B ≤ conjugateSubgroup (m : G) B := by
    rw [hmX]
    exact Subgroup.map_mono (h.le_of_coe_eq rfl)
  have hk : (m : G)⁻¹ * (b * n) ∈ B :=
    (h.conjugate_borel_eq_iff _ _).mp (h.conjugate_borel_eq_of_le _ _ hle)
  have h₁ : (m : G)⁻¹ * b ∈ cell B π (π m⁻¹) :=
    mul_mem_cell_right (mem_cell_of_eq (n := m⁻¹) rfl) hb
  have h₂ : (m : G)⁻¹ * b ∈ cell B π (π n⁻¹) := by
    have : (m : G)⁻¹ * b = (m : G)⁻¹ * (b * n) * ((n⁻¹ : N) : G) := by simp [mul_assoc]
    rw [this]
    exact mul_mem_cell_left (mem_cell_of_eq rfl) hk
  have hmn : π (m⁻¹ * n) = 1 := by
    rw [map_mul, h.eq_of_mem_cell h₁ h₂, ← map_mul, inv_mul_cancel, map_one]
  have ht : ((m⁻¹ * n : N) : G) ∈ B := (h.mem_iff _).mpr hmn
  refine ⟨(m : G)⁻¹ * b * m, ?_, by simp [mul_assoc]⟩
  have : (m : G)⁻¹ * b * m = (m : G)⁻¹ * (b * n) * ((m⁻¹ * n : N) : G)⁻¹ := by
    simp [mul_assoc]
  rw [this]
  exact B.mul_mem hk (B.inv_mem ht)

/-- The stabilizer of the standard restricted apartment for the action by
conjugation: the elements `g` with `g A' g⁻¹ = A'`. -/
def restrictedApartmentStabilizer : Subgroup G where
  carrier := {g | restrictedApartment B π S g = restrictedApartment B π S 1}
  one_mem' := rfl
  mul_mem' {g k} hg hk := by
    change restrictedApartment B π S (g * k) = restrictedApartment B π S 1
    rw [← h.image_conjugateSubgroup_restrictedApartment, hk,
      h.image_conjugateSubgroup_restrictedApartment, mul_one]
    exact hg
  inv_mem' {g} hg := by
    change restrictedApartment B π S g⁻¹ = restrictedApartment B π S 1
    rw [← mul_one g⁻¹, ← h.image_conjugateSubgroup_restrictedApartment, ← hg,
      h.image_conjugateSubgroup_restrictedApartment, inv_mul_cancel]
    exact hg.symm

theorem mem_restrictedApartmentStabilizer {g : G} :
    g ∈ h.restrictedApartmentStabilizer ↔
      restrictedApartment B π S g = restrictedApartment B π S 1 :=
  Iff.rfl

variable (hsat : IsSaturated B N)
include hsat

/-- In a saturated Tits system, an element of `B` whose apartment contains every
chamber of the standard apartment lies in `N`. -/
theorem mem_normalizer_of_forall_mem {b : G} (hb : b ∈ B)
    (hall : ∀ m : N, conjugateSubgroup (m : G) B ∈ restrictedApartment B π S b) : b ∈ N := by
  have hmem : b ∈ ⨅ m : N, B.map (MulAut.conj (m : G)).toMonoidHom :=
    Subgroup.mem_iInf.mpr fun m => h.mem_conjugate_borel_of_mem hb (hall m)
  rw [hsat] at hmem
  exact hmem.2

/-- A restricted apartment containing every chamber of the standard apartment is
the standard apartment. -/
theorem restrictedApartment_eq_one_of_forall {a : G}
    (hall : ∀ m : N, conjugateSubgroup (m : G) B ∈ restrictedApartment B π S a) :
    restrictedApartment B π S a = restrictedApartment B π S 1 := by
  obtain ⟨n, hn⟩ := h.exists_mul_mem_of_borel_mem (by simpa using hall 1)
  rw [← h.restrictedApartment_mul_normalizer a n] at hall ⊢
  have hN := h.mem_normalizer_of_forall_mem hsat hn hall
  rw [← h.restrictedApartment_mul_normalizer 1 ⟨a * n, hN⟩, one_mul]

/-- The stabilizer of the standard restricted apartment is `N`. This internal
deduction from Bruhat disjointness and saturation supplies the equality that
the proof of KP Proposition 7.6.8 attributes to Proposition 1.5.13. -/
theorem mem_normalizer_of_restrictedApartment_eq {g : G}
    (hg : restrictedApartment B π S g = restrictedApartment B π S 1) : g ∈ N := by
  have hB : B ∈ restrictedApartment B π S g := hg ▸ h.borel_mem_restrictedApartment_one
  obtain ⟨n, hn⟩ := h.exists_mul_mem_of_borel_mem hB
  have hall : ∀ m : N, conjugateSubgroup (m : G) B ∈ restrictedApartment B π S (g * n) := by
    intro m
    rw [h.restrictedApartment_mul_normalizer, hg]
    simpa using h.conjugate_borel_mem_restrictedApartment 1 m
  have hgn := h.mem_normalizer_of_forall_mem hsat hn hall
  simpa using N.mul_mem hgn (N.inv_mem n.2)

/-- `restrictedApartment g` is the standard apartment exactly when `g ∈ N`. -/
theorem restrictedApartment_eq_one_iff (g : G) :
    restrictedApartment B π S g = restrictedApartment B π S 1 ↔ g ∈ N := by
  refine ⟨h.mem_normalizer_of_restrictedApartment_eq hsat, fun hg => ?_⟩
  rw [← h.restrictedApartment_mul_normalizer 1 ⟨g, hg⟩, one_mul]

/-- In a saturated Tits system the stabilizer of the standard restricted
apartment is `N`. -/
theorem restrictedApartmentStabilizer_eq : h.restrictedApartmentStabilizer = N :=
  Subgroup.ext fun g => h.restrictedApartment_eq_one_iff hsat g

end IsTitsSystem

end Langlands.Group
