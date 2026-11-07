import Langlands.Group.TitsApartmentPanels

/-! # Gallery incidence between Borel conjugates in a restricted apartment -/

noncomputable section

namespace Langlands.Group

open TitsSystem RelativeWeyl

universe u v

variable {G : Type u} {W : Type v} [Group G] [Group W]
  {B N : Subgroup G} {π : N →* W} {S : Set W}

namespace TitsSystem

/-- An admissible parabolic immediately above `H`, among admissible parabolics. -/
def IsAdmissibleParabolicCover (B : Subgroup G) (π : N →* W) (S : Set W)
    (H Q : Subgroup G) : Prop :=
  IsAdmissibleParabolic B π S Q ∧ H < Q ∧
    ∀ {P : Subgroup G}, IsAdmissibleParabolic B π S P →
      H < P → P ≤ Q → P = Q

/-- Algebraic incidence for a gallery step in the apartment based at `a`.
The panel subgroup covers both endpoints and is their least admissible overgroup. -/
def IsApartmentBorelStep (B : Subgroup G) (π : N →* W) (S : Set W)
    (a : G) (H K : Subgroup G) : Prop :=
  ∃ Q ∈ restrictedApartment B π S a,
    IsAdmissibleParabolicCover B π S H Q ∧
      IsAdmissibleParabolicCover B π S K Q ∧
        ∀ {P : Subgroup G}, IsAdmissibleParabolic B π S P →
          H ≤ P → K ≤ P → Q ≤ P

theorem IsApartmentBorelStep.symm {a : G} {H K : Subgroup G}
    (hHK : IsApartmentBorelStep B π S a H K) :
    IsApartmentBorelStep B π S a K H := by
  obtain ⟨Q, hQ, hH, hK, hleast⟩ := hHK
  exact ⟨Q, hQ, hK, hH, fun hP hKP hHP => hleast hP hHP hKP⟩

end TitsSystem

namespace IsTitsSystem

variable (h : IsTitsSystem B N π S)
include h

/-- Conjugation preserves a cover among admissible parabolics. -/
theorem isAdmissibleParabolicCover_conjugate {H Q : Subgroup G}
    (hHQ : IsAdmissibleParabolicCover B π S H Q) (g : G) :
    IsAdmissibleParabolicCover B π S
      (conjugateSubgroup g H) (conjugateSubgroup g Q) := by
  refine ⟨h.isAdmissibleParabolic_conjugate hHQ.1 g,
    (MulAut.conj g).mapSubgroup.strictMono hHQ.2.1, ?_⟩
  intro P hP hHP hPQ
  have hHP' := (MulAut.conj g⁻¹).mapSubgroup.strictMono hHP
  have hPQ' := Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hPQ
  change conjugateSubgroup g⁻¹ (conjugateSubgroup g H) <
    conjugateSubgroup g⁻¹ P at hHP'
  change conjugateSubgroup g⁻¹ P ≤
    conjugateSubgroup g⁻¹ (conjugateSubgroup g Q) at hPQ'
  simp only [← conjugateSubgroup_mul, inv_mul_cancel, conjugateSubgroup_one] at hHP' hPQ'
  have heq := hHQ.2.2 (h.isAdmissibleParabolic_conjugate hP g⁻¹) hHP' hPQ'
  have H := congrArg (conjugateSubgroup g) heq
  simpa only [← conjugateSubgroup_mul, mul_inv_cancel, conjugateSubgroup_one] using H

/-- An admissible singleton standard parabolic covers the distinguished Borel. -/
theorem isAdmissibleParabolicCover_standardParabolic_singleton {s : W}
    (hs : s ∈ S) (hadm : IsAdmissibleType S {s}) :
    IsAdmissibleParabolicCover B π S B
      (h.standardParabolicSubgroup (Set.singleton_subset_iff.mpr hs)) := by
  let Q := h.standardParabolicSubgroup (Set.singleton_subset_iff.mpr hs)
  have hQadm : IsAdmissibleParabolic B π S Q := by
    refine ⟨1, {s}, hadm, ?_⟩
    simpa only [conjugateSubgroup_one] using
      h.coe_conjugate_standardParabolic (Set.singleton_subset_iff.mpr hs) 1
  have hBQ : B < Q := by
    obtain ⟨n, hn⟩ := h.surjective s
    have hnQ : (n : G) ∈ Q := rep_mem_of_coe_eq rfl
      (by rw [hn]; exact Subgroup.subset_closure (Set.mem_singleton s))
    refine ⟨h.le_of_coe_eq rfl, ?_⟩
    intro hQB
    exact h.ne_one s hs (hn.symm.trans ((h.mem_iff n).mp (hQB hnQ)))
  refine ⟨hQadm, hBQ, ?_⟩
  intro P _ hBP hPQ
  obtain ⟨X, hXS, hPX⟩ := h.exists_eq_standardParabolic P hBP.le
  have hXne : X.Nonempty := by
    by_contra hX
    have hPBeq : P = B := SetLike.coe_injective (by
      rw [hPX, Set.not_nonempty_iff_eq_empty.mp hX, h.standardParabolic_empty])
    exact hBP.ne hPBeq.symm
  obtain ⟨t, htX⟩ := hXne
  obtain ⟨m, hm⟩ := h.surjective t
  have hmP : (m : G) ∈ P := rep_mem_of_coe_eq hPX (hm ▸ Subgroup.subset_closure htX)
  obtain ⟨w, hw, hmw⟩ := hPQ hmP
  have ht : t = 1 ∨ t = s := by
    rw [h.eq_of_mem_cell hmw (coe_mem_cell m), hm] at hw
    exact (h.mem_closure_singleton_iff hs).mp hw
  have hsX : s ∈ X := by
    rcases ht with ht | ht
    · exact False.elim (h.ne_one t (hXS htX) ht)
    · exact ht ▸ htX
  apply le_antisymm hPQ
  rintro x ⟨w, hw, hx⟩
  rw [← SetLike.mem_coe, hPX]
  exact ⟨w, Subgroup.closure_mono (Set.singleton_subset_iff.mpr hsX) hw, hx⟩

/-- The singleton standard parabolic is the least subgroup containing the two
simple-adjacent Borel conjugates. -/
theorem standardParabolic_singleton_le_of_borels_le {s : W} (hs : s ∈ S)
    (n : N) (hn : π n = s) {P : Subgroup G}
    (hBP : B ≤ P) (hnBP : conjugateSubgroup (n : G) B ≤ P) :
    h.standardParabolicSubgroup (Set.singleton_subset_iff.mpr hs) ≤ P := by
  have hnP := (h.conjugate_borel_le_iff hBP (n : G)).mp hnBP
  rintro x ⟨w, hw, hx⟩
  rcases (h.mem_closure_singleton_iff hs).mp hw with hw | hw
  · subst w
    exact hBP ((h.mem_cell_one_iff).mp hx)
  · subst w
    exact h.subset_of_mem hBP hn hnP hx

/-- A simple normalizer lift gives an algebraic gallery step in the same apartment. -/
theorem isApartmentBorelStep_simple {s : W} (hs : s ∈ S)
    (hadm : IsAdmissibleType S {s}) (a : G) (m n : N) (hn : π n = s) :
    IsApartmentBorelStep B π S a
      (conjugateSubgroup (a * m) B) (conjugateSubgroup (a * (m * n)) B) := by
  let Q := h.standardParabolicSubgroup (Set.singleton_subset_iff.mpr hs)
  let g : G := a * m
  have hcov := h.isAdmissibleParabolicCover_standardParabolic_singleton hs hadm
  change IsAdmissibleParabolicCover B π S B Q at hcov
  have hnQ : (n : G) ∈ Q := rep_mem_of_coe_eq rfl
    (by rw [hn]; exact Subgroup.subset_closure (Set.mem_singleton s))
  have hcovn : IsAdmissibleParabolicCover B π S (conjugateSubgroup (n : G) B) Q := by
    simpa only [conjugateSubgroup_eq_self hnQ] using
      h.isAdmissibleParabolicCover_conjugate hcov (n : G)
  refine ⟨conjugateSubgroup g Q,
    h.mem_restrictedApartment_iff_conjugate.mpr ⟨m, {s}, hadm, rfl⟩,
    h.isAdmissibleParabolicCover_conjugate hcov g, ?_, ?_⟩
  · simpa only [← conjugateSubgroup_mul, g, Subgroup.coe_mul, mul_assoc] using
      h.isAdmissibleParabolicCover_conjugate hcovn g
  · intro P _ hHP hKP
    have hB := Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hHP
    have hK0 : conjugateSubgroup (g * n) B ≤ P := by
      simpa only [g, Subgroup.coe_mul, mul_assoc] using hKP
    have hK := Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hK0
    change conjugateSubgroup g⁻¹ (conjugateSubgroup g B) ≤
      conjugateSubgroup g⁻¹ P at hB
    change conjugateSubgroup g⁻¹ (conjugateSubgroup (g * n) B) ≤
      conjugateSubgroup g⁻¹ P at hK
    simp only [← conjugateSubgroup_mul, inv_mul_cancel, inv_mul_cancel_left,
      conjugateSubgroup_one] at hB hK
    have H := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom)
      (h.standardParabolic_singleton_le_of_borels_le hs n hn hB hK)
    change conjugateSubgroup g Q ≤
      conjugateSubgroup g (conjugateSubgroup g⁻¹ P) at H
    simpa only [← conjugateSubgroup_mul, mul_inv_cancel, conjugateSubgroup_one] using H

/-- If singleton types are admissible, any two normalizer Borel conjugates in an
apartment are joined by algebraic gallery steps. -/
theorem reflTransGen_isApartmentBorelStep
    (hadm : ∀ s ∈ S, IsAdmissibleType S {s}) (a : G) (m n : N) :
    Relation.ReflTransGen (IsApartmentBorelStep B π S a)
      (conjugateSubgroup (a * m) B) (conjugateSubgroup (a * n) B) := by
  have hword : ∀ (l : List W), (∀ s ∈ l, s ∈ S) →
      ∀ (m n : N), π n = l.prod →
        Relation.ReflTransGen (IsApartmentBorelStep B π S a)
          (conjugateSubgroup (a * m) B) (conjugateSubgroup (a * (m * n)) B) := by
    intro l hl
    induction l with
    | nil =>
      intro m n hn
      have hnB : (n : G) ∈ B := (h.mem_iff n).mpr (by simpa using hn)
      have heq : conjugateSubgroup (a * (m * n)) B = conjugateSubgroup (a * m) B := by
        rw [← mul_assoc, conjugateSubgroup_mul,
          conjugateSubgroup_eq_self hnB]
      rw [heq]
    | cons s l ih =>
      intro m n hn
      have hs : s ∈ S := hl s (by simp)
      obtain ⟨ns, hns⟩ := h.surjective s
      have hn' : π (ns⁻¹ * n) = l.prod := by
        simp only [List.prod_cons] at hn
        simp [map_mul, map_inv, hns, hn]
      have htail := ih (fun t ht => hl t (by simp [ht])) (m * ns) (ns⁻¹ * n) hn'
      have hstep := h.isApartmentBorelStep_simple hs (hadm s hs) a m ns hns
      have H := Relation.ReflTransGen.head hstep htail
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc, mul_inv_cancel_left] using H
  obtain ⟨l, hl, heq⟩ := exists_word_of_mem_closure h.mul_self
    (h.closure_eq ▸ Subgroup.mem_top (π (m⁻¹ * n)))
  have H := hword l hl m (m⁻¹ * n) heq.symm
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left] using H

end IsTitsSystem
end Langlands.Group
