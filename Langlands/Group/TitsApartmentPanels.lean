import Langlands.Group.TitsApartmentFaces
import Langlands.Group.TitsBorelThickness

/-! # Two Borel conjugates over a panel in a restricted apartment -/

noncomputable section

namespace Langlands.Group

open TitsSystem RelativeWeyl

universe u v

variable {G : Type u} {W : Type v} [Group G] [Group W]
  {B N : Subgroup G} {π : N →* W} {S : Set W}

namespace TitsSystem

/-- The normalizer Borel conjugates in the apartment based at `a`, contained in `Q`. -/
def apartmentBorelsBelow (B N : Subgroup G) (a : G) (Q : Subgroup G) :
    Set (Subgroup G) :=
  {H | (∃ n : N, H = conjugateSubgroup (a * n) B) ∧ H ≤ Q}

theorem apartmentBorelsBelow_mul_normalizer (a : G) (n : N) (Q : Subgroup G) :
    apartmentBorelsBelow B N (a * n) Q = apartmentBorelsBelow B N a Q := by
  ext H
  constructor
  · rintro ⟨⟨m, hm⟩, hle⟩
    exact ⟨⟨n * m, by simpa only [Subgroup.coe_mul, mul_assoc] using hm⟩, hle⟩
  · rintro ⟨⟨m, hm⟩, hle⟩
    refine ⟨⟨n⁻¹ * m, ?_⟩, hle⟩
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc, mul_inv_cancel_left] using hm

theorem image_conjugateSubgroup_apartmentBorelsBelow (g a : G) (Q : Subgroup G) :
    conjugateSubgroup g '' apartmentBorelsBelow B N a Q =
      apartmentBorelsBelow B N (g * a) (conjugateSubgroup g Q) := by
  ext H
  constructor
  · rintro ⟨K, ⟨⟨n, rfl⟩, hle⟩, rfl⟩
    exact ⟨⟨n, by rw [← conjugateSubgroup_mul, mul_assoc]⟩, Subgroup.map_mono hle⟩
  · rintro ⟨⟨n, rfl⟩, hle⟩
    refine ⟨conjugateSubgroup (a * n) B, ⟨⟨n, rfl⟩, ?_⟩, ?_⟩
    · have H := Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hle
      change conjugateSubgroup g⁻¹ (conjugateSubgroup (g * a * n) B) ≤
        conjugateSubgroup g⁻¹ (conjugateSubgroup g Q) at H
      simpa only [← conjugateSubgroup_mul, mul_assoc, inv_mul_cancel_left,
        inv_mul_cancel, conjugateSubgroup_one] using H
    · rw [← conjugateSubgroup_mul, mul_assoc]

theorem IsAdmissibleType.mono {X Y : Set W} (hX : IsAdmissibleType S X) (hYX : Y ⊆ X) :
    IsAdmissibleType S Y := by
  refine ⟨hYX.trans hX.1, ?_⟩
  intro s hs
  obtain ⟨t, htS, hst, htX⟩ := hX.2 s hs
  exact ⟨t, htS, hst, fun htY => htX (hYX htY)⟩

end TitsSystem

namespace IsTitsSystem

variable (h : IsTitsSystem B N π S)
include h

/-- Membership may equivalently use the existing restricted apartment and Borel sets. -/
theorem apartmentBorelsBelow_eq_inter (a : G) (Q : Subgroup G) :
    apartmentBorelsBelow B N a Q = borelsBelow B Q ∩ restrictedApartment B π S a := by
  ext H
  constructor
  · rintro ⟨⟨n, rfl⟩, hle⟩
    refine ⟨⟨⟨a * n, rfl⟩, hle⟩,
      h.mem_restrictedApartment_iff_conjugate.mpr ⟨n, ∅, isAdmissibleType_empty S, ?_⟩⟩
    rw [show h.standardParabolicSubgroup (Set.empty_subset S) = B from
      SetLike.coe_injective h.standardParabolic_empty]
  · rintro ⟨⟨⟨g, rfl⟩, hle⟩, hapt⟩
    obtain ⟨n, _, hnle⟩ := h.exists_conjugate_borel_le_in_restrictedApartment hapt
    exact ⟨⟨n, (h.conjugate_borel_eq_of_le (a * n) g hnle).symm⟩, hle⟩

/-- A simple reflection generates only itself and the identity. -/
theorem mem_closure_singleton_iff {s w : W} (hs : s ∈ S) :
    w ∈ Subgroup.closure ({s} : Set W) ↔ w = 1 ∨ w = s := by
  constructor
  · intro hw
    induction hw using Subgroup.closure_induction with
    | mem x hx => exact Or.inr (Set.mem_singleton_iff.mp hx)
    | one => exact Or.inl rfl
    | mul x y _ _ hx hy =>
      rcases hx with hx | hx <;> rcases hy with hy | hy
      · exact Or.inl (by rw [hx, hy, one_mul])
      · exact Or.inr (by rw [hx, hy, one_mul])
      · exact Or.inr (by rw [hx, hy, mul_one])
      · exact Or.inl (by rw [hx, hy]; exact h.mul_self s hs)
    | inv x _ hx =>
      rcases hx with hx | hx
      · exact Or.inl (by rw [hx, inv_one])
      · exact Or.inr (by rw [hx]; exact h.inv_eq hs)
  · rintro (hw | hw)
    · rw [hw]
      exact Subgroup.one_mem _
    · rw [hw]
      exact Subgroup.subset_closure (Set.mem_singleton s)

/-- An admissible cover of `B` has a singleton standard-parabolic type. -/
theorem exists_eq_standardParabolic_singleton_of_cover {Q : Subgroup G}
    (hQ : IsAdmissibleParabolic B π S Q) (hBQ : B < Q)
    (hcover : ∀ {P : Subgroup G}, IsAdmissibleParabolic B π S P →
      B < P → P ≤ Q → P = Q) :
    ∃ (s : W) (hs : s ∈ S),
      Q = h.standardParabolicSubgroup (Set.singleton_subset_iff.mpr hs) := by
  obtain ⟨X, hX, hQX⟩ := h.exists_admissible_standardParabolic_eq hQ hBQ.le
  have hXne : X.Nonempty := by
    by_contra hempty
    have hX0 := Set.not_nonempty_iff_eq_empty.mp hempty
    have hQB : Q = B := by
      apply SetLike.coe_injective
      rw [hQX, h.coe_standardParabolicSubgroup, hX0, h.standardParabolic_empty]
    exact (ne_of_lt hBQ) hQB.symm
  obtain ⟨s, hsX⟩ := hXne
  have hs : s ∈ S := hX.1 hsX
  have hsing := Set.singleton_subset_iff.mpr hs
  let P := h.standardParabolicSubgroup hsing
  have hPadm : IsAdmissibleParabolic B π S P := by
    refine ⟨1, {s}, hX.mono (Set.singleton_subset_iff.mpr hsX), ?_⟩
    simpa only [conjugateSubgroup_one] using h.coe_conjugate_standardParabolic hsing 1
  have hBP : B < P := by
    obtain ⟨n, hn⟩ := h.surjective s
    have hnP : (n : G) ∈ P := rep_mem_of_coe_eq rfl
      (by rw [hn]; exact Subgroup.subset_closure (Set.mem_singleton s))
    refine ⟨h.le_of_coe_eq rfl, ?_⟩
    intro hPB
    exact h.ne_one s hs (hn.symm.trans ((h.mem_iff n).mp (hPB hnP)))
  have hPQ : P ≤ Q := by
    rintro x ⟨w, hw, hx⟩
    rw [hQX]
    exact ⟨w, Subgroup.closure_mono (Set.singleton_subset_iff.mpr hsX) hw, hx⟩
  exact ⟨s, hs, (hcover hPadm hBP hPQ).symm⟩

/-- Exactly the identity and simple-reflection Borels occur below a singleton parabolic. -/
theorem apartmentBorelsBelow_standardParabolic_singleton {s : W} (hs : s ∈ S)
    (n : N) (hn : π n = s) :
    apartmentBorelsBelow B N 1
        (h.standardParabolicSubgroup (Set.singleton_subset_iff.mpr hs)) =
      {B, conjugateSubgroup (n : G) B} := by
  let Q := h.standardParabolicSubgroup (Set.singleton_subset_iff.mpr hs)
  have hBQ : B ≤ Q := h.le_of_coe_eq rfl
  ext H
  constructor
  · rintro ⟨⟨m, rfl⟩, hle⟩
    have hmQ : (m : G) ∈ Q := (h.conjugate_borel_le_iff hBQ _).mp (by
      simpa only [one_mul] using hle)
    obtain ⟨w, hw, hmw⟩ := hmQ
    have hm : π m = 1 ∨ π m = s := by
      rw [h.eq_of_mem_cell hmw (coe_mem_cell m)] at hw
      exact (h.mem_closure_singleton_iff hs).mp hw
    rcases hm with hm | hm
    · exact Or.inl (by
        simpa only [one_mul] using conjugateSubgroup_eq_self ((h.mem_iff m).mpr hm))
    · exact Or.inr (by
        simp only [Set.mem_singleton_iff, one_mul]
        apply (h.conjugate_borel_eq_iff _ _).mpr
        exact (h.mem_iff (n⁻¹ * m)).mpr (by simp [hn, hm]))
  · rintro (rfl | rfl)
    · exact ⟨⟨1, by simp⟩, hBQ⟩
    · refine ⟨⟨n, by simp⟩, (h.conjugate_borel_le_iff hBQ _).mpr ?_⟩
      exact rep_mem_of_coe_eq rfl
        (by rw [hn]; exact Subgroup.subset_closure (Set.mem_singleton s))

theorem encard_apartmentBorelsBelow_eq_two_of_cover {Q : Subgroup G}
    (hQ : IsAdmissibleParabolic B π S Q) (hBQ : B < Q)
    (hcover : ∀ {P : Subgroup G}, IsAdmissibleParabolic B π S P →
      B < P → P ≤ Q → P = Q) :
    (apartmentBorelsBelow B N 1 Q).encard = 2 := by
  obtain ⟨s, hs, rfl⟩ := h.exists_eq_standardParabolic_singleton_of_cover hQ hBQ hcover
  obtain ⟨n, hn⟩ := h.surjective s
  rw [h.apartmentBorelsBelow_standardParabolic_singleton hs n hn]
  apply Set.encard_eq_two.mpr
  refine ⟨B, conjugateSubgroup (n : G) B, ?_, rfl⟩
  intro heq
  exact h.ne_one s hs (hn.symm.trans
    ((h.mem_iff n).mp ((h.conjugate_borel_eq_self_iff _).mp heq.symm)))

/-- The two-count is invariant under conjugation of an admissible cover. -/
theorem encard_apartmentBorelsBelow_eq_two_of_conjugate_cover {Q : Subgroup G}
    (a : G) (hQ : IsAdmissibleParabolic B π S Q)
    (hBQ : conjugateSubgroup a B < Q)
    (hcover : ∀ {P : Subgroup G}, IsAdmissibleParabolic B π S P →
      conjugateSubgroup a B < P → P ≤ Q → P = Q) :
    (apartmentBorelsBelow B N a Q).encard = 2 := by
  let Q' := conjugateSubgroup a⁻¹ Q
  have hBQ' : B < Q' := by
    have H := ((MulAut.conj a⁻¹).mapSubgroup).strictMono hBQ
    change conjugateSubgroup a⁻¹ (conjugateSubgroup a B) < Q' at H
    simpa only [← conjugateSubgroup_mul, inv_mul_cancel, conjugateSubgroup_one] using H
  have hcover' : ∀ {P : Subgroup G}, IsAdmissibleParabolic B π S P →
      B < P → P ≤ Q' → P = Q' := by
    intro P hP hBP hPQ
    have hBP' := ((MulAut.conj a).mapSubgroup).strictMono hBP
    have hPQ' : conjugateSubgroup a P ≤ Q := by
      have H := Subgroup.map_mono (f := (MulAut.conj a).toMonoidHom) hPQ
      change conjugateSubgroup a P ≤ conjugateSubgroup a Q' at H
      simpa only [Q', ← conjugateSubgroup_mul, mul_inv_cancel,
        conjugateSubgroup_one] using H
    have heq := congrArg (conjugateSubgroup a⁻¹)
      (hcover (h.isAdmissibleParabolic_conjugate hP a) hBP' hPQ')
    simpa only [← conjugateSubgroup_mul, inv_mul_cancel, conjugateSubgroup_one] using heq
  have hcount := h.encard_apartmentBorelsBelow_eq_two_of_cover
    (h.isAdmissibleParabolic_conjugate hQ a⁻¹) hBQ' hcover'
  have heq := image_conjugateSubgroup_apartmentBorelsBelow (B := B) (N := N) a 1 Q'
  have hconj : conjugateSubgroup a Q' = Q := by
    simp only [Q', ← conjugateSubgroup_mul, mul_inv_cancel, conjugateSubgroup_one]
  rw [mul_one, hconj] at heq
  have hinj : Function.Injective (conjugateSubgroup a : Subgroup G → Subgroup G) :=
    ((MulAut.conj a).mapSubgroup).injective
  rw [← heq, hinj.encard_image]
  exact hcount

end IsTitsSystem
end Langlands.Group
