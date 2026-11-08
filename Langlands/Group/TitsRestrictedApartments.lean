import Langlands.Group.TitsRestrictedPolysimplicial
import Langlands.Group.TitsApartmentFaces
import Langlands.Geometry.Building.PolysimplicialSubcomplex

/-! # Apartments of the restricted building are polysimplicial -/

namespace Langlands.Group

open TitsSystem RelativeWeyl Langlands.Geometry.Building

namespace IsTitsSystem

variable {G W : Type*} [Group G] [Group W]
  {B N : Subgroup G} {π : N →* W} {S : Set W}
  (h : IsTitsSystem B N π S)
include h

/-- Cosets of the complements `W_{S \ S_c}` of all components have a common
point. -/
theorem exists_forall_inv_mul_mem_closure [Finite S] (w : Component S → W) :
    ∃ v : W, ∀ c, (w c)⁻¹ * v ∈ Subgroup.closure (S \ componentSet c) := by
  classical
  have : Fintype (Component S) := Fintype.ofFinite _
  suffices ∀ J : Finset (Component S), ∃ v : W, ∀ c ∈ J,
      (w c)⁻¹ * v ∈ Subgroup.closure (S \ componentSet c) by
    obtain ⟨v, hv⟩ := this Finset.univ
    exact ⟨v, fun c => hv c (Finset.mem_univ c)⟩
  intro J
  induction J using Finset.induction_on with
  | empty => exact ⟨1, by simp⟩
  | insert m J hm ih =>
    obtain ⟨v, hv⟩ := ih
    let T : Set W := {s | ∃ c ∈ J, s ∈ componentSet c}
    have hcomm : ∀ t ∈ T, ∀ s ∈ S \ T, t * s = s * t := by
      rintro t ⟨c, hc, htc⟩ s ⟨hsS, hsT⟩
      exact commute_of_not_mem_componentSet htc hsS fun hsc => hsT ⟨c, hc, hsc⟩
    obtain ⟨u, hu, t, ht, hut⟩ := h.exists_mul_eq_of_commute hcomm (v⁻¹ * w m)
    have hu' : u = v⁻¹ * w m * t⁻¹ := eq_mul_inv_of_mul_eq hut.symm
    have hm' : (w m)⁻¹ * (v * u) ∈ Subgroup.closure (S \ componentSet m) := by
      have heq : (w m)⁻¹ * (v * u) = t⁻¹ := by rw [hu']; simp [mul_assoc]
      rw [heq]
      refine Subgroup.closure_mono ?_ (Subgroup.inv_mem _ ht)
      rintro s ⟨d, hd, hsd⟩
      refine ⟨componentSet_subset d hsd, fun hsm => ?_⟩
      exact hm (eq_of_mem_componentSet hsd hsm ▸ hd)
    refine ⟨v * u, fun c hc => ?_⟩
    rcases Finset.mem_insert.mp hc with rfl | hc
    · exact hm'
    · rw [← mul_assoc]
      exact Subgroup.mul_mem _ (hv c hc) (Subgroup.closure_mono
        (Set.sdiff_subset_sdiff_right (show componentSet c ⊆ T from fun s hs => ⟨c, hc, hs⟩))
        hu)

/-- The face of a component depends only on the coset modulo the complement
of the component and on the part of the type in the component. -/
theorem componentFace_eq_of_inv_mul_mem {c : Component S} {X Y : Set W} (hX : X ⊆ S)
    (hY : Y ⊆ S) {x y : G}
    (hxy : x⁻¹ * y ∈ h.standardParabolicSubgroup (Set.sdiff_subset : S \ componentSet c ⊆ S))
    (hXY : ∀ s ∈ componentSet c, (s ∈ X ↔ s ∈ Y)) :
    h.componentFace c (conjugateSubgroup x (h.standardParabolicSubgroup hX)) =
      h.componentFace c (conjugateSubgroup y (h.standardParabolicSubgroup hY)) := by
  ext Q
  rw [mem_componentFace, mem_componentFace,
    h.conjugate_le_iff_of_isComponentVertex hX x Q.2,
    h.conjugate_le_iff_of_isComponentVertex hY y Q.2]
  refine exists_congr fun s => and_congr_right fun hs => and_congr (not_congr (hXY s hs)) ?_
  have hk : x⁻¹ * y ∈ h.standardParabolicSubgroup (Set.sdiff_subset : S \ {s} ⊆ S) :=
    (h.standardParabolicSubgroup_le_iff Set.sdiff_subset Set.sdiff_subset).mpr
      (Set.sdiff_subset_sdiff_right (Set.singleton_subset_iff.mpr hs)) hxy
  have := h.maximalParabolic_mul_of_mem (g := x) hk
  rw [mul_inv_cancel_left] at this
  rw [this]

variable [Finite S]

/-- The coordinate projection of the product attached to an admissible
parabolic subgroup is its component face. -/
theorem eval_image_restrictedBox {P : Subgroup G} (hP : IsAdmissibleParabolic B π S P)
    (c : Component S) :
    (fun x => x c) '' h.restrictedBox P = h.componentFace c P :=
  Set.eval_image_univ_pi
    (AbstractBuilding.PolysimplicialComplex.nonempty_of_mem_facets
      (h.restrictedBox_mem_facets hP))

/-- The facets of the restricted apartment based at `a`, as products of
component simplices. -/
def restrictedApartmentBoxes (a : G) : Set (Set (∀ c, h.ComponentVertex c)) :=
  {F | ∃ P ∈ restrictedApartment B π S a, F = h.restrictedBox P}

theorem isSubcomplex_restrictedApartmentBoxes (a : G) :
    AbstractBuilding.IsSubcomplex (h.restrictedApartmentBoxes a) h.restrictedComplex.facets := by
  refine ⟨?_, ?_⟩
  · rintro F ⟨P, hP, rfl⟩
    exact h.restrictedBox_mem_facets (isAdmissibleParabolic_of_mem_restrictedApartment hP)
  · rintro A ⟨P, hP, rfl⟩ C hC hCA
    obtain ⟨P', hP', rfl⟩ := h.exists_restrictedBox_eq hC
    have hle : P ≤ P' := (h.restrictedBox_subset_iff hP').mp hCA
    exact ⟨P', h.mem_restrictedApartment_of_le hP hP' hle, rfl⟩

omit [Finite S] in
theorem restrictedApartmentBoxes_nonempty (a : G) : (h.restrictedApartmentBoxes a).Nonempty :=
  ⟨_, _, h.mem_restrictedApartment_iff_conjugate.mpr
    ⟨1, ∅, isAdmissibleType_empty S, rfl⟩, rfl⟩

/-- Component simplices of facets of one restricted apartment can be combined
(the mixing step of KP Proposition 1.5.18(1) for apartments). -/
theorem isCoordinateMixingClosed_restrictedApartmentBoxes (a : G) :
    AbstractBuilding.PolysimplicialComplex.IsCoordinateMixingClosed
      (h.restrictedApartmentBoxes a) := by
  intro F
  choose P hPa hPF using fun c => (F c).2
  choose n X hX hnX using fun c => h.mem_restrictedApartment_iff_conjugate.mp (hPa c)
  obtain ⟨v, hv⟩ := h.exists_forall_inv_mul_mem_closure (fun c => π (n c))
  obtain ⟨m, hm⟩ := h.surjective v
  let Y : Set W := {s | ∃ c, s ∈ componentSet c ∧ s ∈ X c}
  have hmemY : ∀ {c : Component S} {s : W}, s ∈ componentSet c → (s ∈ X c ↔ s ∈ Y) := by
    intro c s hs
    constructor
    · intro hsX
      exact ⟨c, hs, hsX⟩
    · rintro ⟨d, hd, hsd⟩
      rwa [eq_of_mem_componentSet hs hd]
  have hY : IsAdmissibleType S Y := by
    refine isAdmissibleType_iff.mpr ⟨fun s ⟨c, hs, _⟩ => componentSet_subset c hs, fun c => ?_⟩
    obtain ⟨t, ht, htX⟩ := (isAdmissibleType_iff.mp (hX c)).2 c
    exact ⟨t, ht, fun htY => htX ((hmemY ht).mpr htY)⟩
  refine ⟨_, h.mem_restrictedApartment_iff_conjugate.mpr ⟨m, Y, hY, rfl⟩,
    congrArg Set.univ.pi (funext fun c => ?_)⟩
  rw [hPF c, h.eval_image_restrictedBox
    (isAdmissibleParabolic_of_mem_restrictedApartment (hPa c)) c, hnX c]
  refine h.componentFace_eq_of_inv_mul_mem (hX c).1 hY.1 ?_ fun s hs => hmemY hs
  have hcoe : (a * ((n c : N) : G))⁻¹ * (a * ((m : N) : G)) = (((n c)⁻¹ * m : N) : G) := by
    simp [mul_assoc]
  rw [hcoe]
  exact ⟨_, by simpa [hm] using hv c, mem_cell_of_eq rfl⟩

/-- Every restricted apartment is a polysimplicial complex (KP
Proposition 1.5.18(1) and (3), polysimplicial part for apartments). -/
theorem isPolysimplicial_restrictedApartmentBoxes (a : G) :
    AbstractBuilding.IsPolysimplicial (h.restrictedApartmentBoxes a) :=
  h.restrictedComplex.isPolysimplicial_of_coordinateMixingClosed
    (h.isSubcomplex_restrictedApartmentBoxes a) (h.restrictedApartmentBoxes_nonempty a)
    (h.isCoordinateMixingClosed_restrictedApartmentBoxes a)

end IsTitsSystem

end Langlands.Group
