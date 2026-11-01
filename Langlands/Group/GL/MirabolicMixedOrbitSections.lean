import Langlands.Group.GL.MirabolicMixedOrbitData

/-! Concrete lower-rank sections of the actual mixed orbit stabilizers. -/

namespace Langlands.GeneralLinear.Mirabolic.MixedOrbit

open Langlands.GeneralLinear.Mirabolic.MixedProduct

universe u

section EntryCriteria

variable {R : Type u} [CommRing R] {k r : ℕ}

private theorem mem_leftSubgroup_iff_bounds (g : mirabolic (k + r) R) :
    g ∈ leftSubgroup k r R ↔
      ∀ i j : Fin (k + r + 1), k ≤ i.val → j.val < k → g.val.val i j = 0 := by
  rw [mem_leftSubgroup_iff_entry]
  constructor
  · intro h i j hi hj
    have he₁ : leftIndex k r (Sum.inr ⟨i.val - k, by omega⟩) = i := by
      apply Fin.ext
      simp only [leftIndex_inr_val]
      omega
    have he₂ : leftIndex k r (Sum.inl ⟨j.val, hj⟩) = j := by
      apply Fin.ext
      simp
    simpa only [he₁, he₂] using h ⟨i.val - k, by omega⟩ ⟨j.val, hj⟩
  · intro h i j
    exact h _ _ (by simp) (by simp)

private theorem mem_rightSubgroup_iff_bounds (g : mirabolic (k + r) R) :
    g ∈ rightSubgroup k r R ↔
      ∀ i j : Fin (k + r + 1), r ≤ i.val → i.val < r + k →
        (j.val < r ∨ j = Fin.last (k + r)) → g.val.val i j = 0 := by
  rw [mem_rightSubgroup_iff_entry]
  constructor
  · intro h i j hi hi' hj
    have he₁ : rightIndex k r (Sum.inr ⟨i.val - r, by omega⟩) = i := by
      apply Fin.ext
      simp only [rightIndex_middle_val]
      omega
    rcases hj with hj | rfl
    · have he₂ : rightIndex k r (Sum.inl (⟨j.val, hj⟩ : Fin r).castSucc) = j := by
        apply Fin.ext
        exact rightIndex_first_val (⟨j.val, hj⟩ : Fin r)
      simpa only [he₁, he₂] using
        h ⟨i.val - r, by omega⟩ (⟨j.val, hj⟩ : Fin r).castSucc
    · simpa only [he₁, rightIndex_last] using h ⟨i.val - r, by omega⟩ (Fin.last r)
  · intro h i j
    apply h
    · simp
    · simp only [rightIndex_middle_val]
      omega
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · exact Or.inr rightIndex_last
      · exact Or.inl (by simp)

private theorem rankCast_mem_left_iff {n : ℕ} (h : k + r = n) (g : mirabolic n R) :
    (rankCast h).symm g ∈ leftSubgroup k r R ↔
      ∀ i j : Fin (n + 1), k ≤ i.val → j.val < k → g.val.val i j = 0 := by
  subst h
  rw [mem_leftSubgroup_iff_bounds]
  rfl

private theorem rankCast_mem_right_iff {n : ℕ} (h : k + r = n) (g : mirabolic n R) :
    (rankCast h).symm g ∈ rightSubgroup k r R ↔
      ∀ i j : Fin (n + 1), r ≤ i.val → i.val < r + k →
        (j.val < r ∨ j = Fin.last n) → g.val.val i j = 0 := by
  subst h
  rw [mem_rightSubgroup_iff_bounds]
  rfl

end EntryCriteria

section IdentitySections

variable {R : Type u} [CommRing R] (k r : ℕ)

/-- At the left identity orbit, the actual section is the lower left mixed subgroup. -/
theorem mem_leftSection_one_iff (g : mirabolic (k + r + 1) R) :
    g ∈ leftSection k r R 1 ↔
      (rankCast (show k + 1 + r = k + r + 1 by omega)).symm g ∈
        leftSubgroup (k + 1) r R := by
  rw [mem_sectionSubgroup_iff, leftRepresentative_one, inv_one, one_mul, mul_one,
    mem_leftInducing_iff, rankCast_mem_left_iff, rankCast_mem_left_iff]
  constructor
  · intro h i j hi hj
    simpa only [successor_first] using h i.castSucc j.castSucc hi hj
  · intro h i j hi hj
    revert hi
    refine Fin.lastCases ?_ (fun i => ?_) i
    · intro _
      rw [(successor g).property]
      have hne : j ≠ Fin.last (k + r + 2) := by
        intro he
        have := congrArg Fin.val he
        simp only [Fin.val_last] at this
        omega
      simp only [hne, ↓reduceIte]
    · intro hi
      have hj' : j.val < k + r + 2 := by omega
      have he : (⟨j.val, hj'⟩ : Fin (k + r + 2)).castSucc = j := Fin.ext rfl
      rw [← he, successor_first]
      exact h i ⟨j.val, hj'⟩ hi hj

/-- At the right identity orbit, the lower mixed subgroup has its two blocks reversed. -/
theorem mem_rightSection_one_iff (g : mirabolic (k + r + 1) R) :
    g ∈ rightSection k r R 1 ↔
      (rankCast (show r + 1 + k = k + r + 1 by omega)).symm g ∈
        leftSubgroup (r + 1) k R := by
  rw [mem_sectionSubgroup_iff, rightRepresentative_one, inv_one, one_mul, mul_one,
    mem_rightInducing_iff, rankCast_mem_right_iff, rankCast_mem_left_iff]
  constructor
  · intro h i j hi hj
    simpa only [successor_first] using
      h i.castSucc j.castSucc hi (by change i.val < r + 1 + (k + 1); omega) (Or.inl hj)
  · intro h i j hi hi' hj
    have hi'' : i.val < k + r + 2 := by omega
    have hei : (⟨i.val, hi''⟩ : Fin (k + r + 2)).castSucc = i := Fin.ext rfl
    rw [← hei]
    rcases hj with hj | rfl
    · have hj' : j.val < k + r + 2 := by omega
      have hej : (⟨j.val, hj'⟩ : Fin (k + r + 2)).castSucc = j := Fin.ext rfl
      rw [← hej, successor_first]
      exact h _ _ hi hj
    · exact successor_last g _

end IdentitySections

section RightCycleSection

variable {R : Type u} [CommRing R] (k r : ℕ)

private theorem cycle_inv_conjugate_entry {t a : ℕ} (ha : a ≤ t)
    (g : mirabolic (t + 1) R) (i j : Fin (t + 2)) :
    ((cycleElement t a ha R)⁻¹ * g * cycleElement t a ha R).val.val i j =
      g.val.val (descendingCycle t a ha i) (descendingCycle t a ha j) := by
  change ((permutation (t + 2) R (descendingCycle t a ha))⁻¹ * g.val *
    permutation (t + 2) R (descendingCycle t a ha)).val i j = _
  rw [mul_permutation_entry, permutation_inv, permutation_mul_entry]
  rfl

private theorem rightCycle_middle (i : Fin (k + r + 3))
    (hi : r < i.val) (hi' : i.val ≤ k + r + 1) :
    descendingCycle (k + r + 1) r (by omega) i =
      (⟨i.val - 1, by omega⟩ : Fin (k + r + 2)).castSucc := by
  apply Fin.ext
  change (if i.val = r then _ else if r < i.val ∧ i.val ≤ k + r + 1 then _ else _) = _
  rw [ite_eq_right (by omega), ite_eq_left ⟨hi, hi'⟩]
  rfl

private theorem rightCycle_first (j : Fin (k + r + 3)) (hj : j.val < r) :
    descendingCycle (k + r + 1) r (by omega) j =
      (⟨j.val, by omega⟩ : Fin (k + r + 2)).castSucc := by
  apply Fin.ext
  change (if j.val = r then _ else if r < j.val ∧ j.val ≤ k + r + 1 then _ else _) = _
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  rfl

private theorem rightCycle_start (j : Fin (k + r + 3)) (hj : j.val = r) :
    descendingCycle (k + r + 1) r (by omega) j =
      (Fin.last (k + r + 1)).castSucc := by
  apply Fin.ext
  change (if j.val = r then _ else _) = _
  rw [ite_eq_left hj]
  rfl

/-- At the right cyclic orbit, the actual section is the lower right mixed subgroup. -/
theorem mem_rightSection_zero_iff (g : mirabolic (k + r + 1) R) :
    g ∈ rightSection k r R 0 ↔
      (rankCast (show k + 1 + r = k + r + 1 by omega)).symm g ∈
        rightSubgroup (k + 1) r R := by
  rw [mem_sectionSubgroup_iff, rightRepresentative_zero, mem_rightInducing_iff,
    rankCast_mem_right_iff, rankCast_mem_right_iff]
  simp only [rightCycleElement, cycle_inv_conjugate_entry]
  constructor
  · intro h i j hi hi' hj
    let i' : Fin (k + r + 3) := ⟨i.val + 1, by omega⟩
    have hei : descendingCycle (k + r + 1) r (by omega) i' = i.castSucc := by
      rw [rightCycle_middle k r i' (by dsimp [i']; omega) (by dsimp [i']; omega)]
      apply Fin.ext
      change i.val + 1 - 1 = i.val
      omega
    rcases hj with hj | rfl
    · let j' : Fin (k + r + 3) := ⟨j.val, by omega⟩
      have hej : descendingCycle (k + r + 1) r (by omega) j' = j.castSucc := by
        rw [rightCycle_first k r j' hj]
      simpa only [hei, hej, successor_first] using
        h i' j' (by dsimp [i']; omega) (by dsimp [i']; omega) (Or.inl (by dsimp [j']; omega))
    · let j' : Fin (k + r + 3) := ⟨r, by omega⟩
      have hej := rightCycle_start k r j' rfl
      simpa only [hei, hej, successor_first] using
        h i' j' (by dsimp [i']; omega) (by dsimp [i']; omega) (Or.inl (by dsimp [j']; omega))
  · intro h i j hi hi' hj
    rw [rightCycle_middle k r i (by omega) (by omega)]
    rcases hj with hj | rfl
    · by_cases hj' : j.val < r
      · rw [rightCycle_first k r j hj', successor_first]
        exact h _ _ (by dsimp; omega) (by dsimp; omega) (Or.inl hj')
      · rw [rightCycle_start k r j (by omega), successor_first]
        exact h _ _ (by dsimp; omega) (by dsimp; omega) (Or.inr rfl)
    · rw [descendingCycle_last]
      exact successor_last g _

end RightCycleSection

section Equivalences

private def restrictEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (A : Subgroup G) (B : Subgroup H) (h : ∀ g, g ∈ A ↔ e g ∈ B) : A ≃* B where
  toFun g := ⟨e g.val, (h g.val).mp g.property⟩
  invFun g := ⟨e.symm g.val, (h _).mpr (by
    simpa only [e.apply_symm_apply] using g.property)⟩
  left_inv g := Subtype.ext (e.symm_apply_apply g.val)
  right_inv g := Subtype.ext (e.apply_symm_apply g.val)
  map_mul' g g' := Subtype.ext (e.map_mul g.val g'.val)

variable (k r : ℕ) (R : Type u) [CommRing R]

/-- The actual left identity section, in lower left mixed-product coordinates. -/
def leftIdentitySectionEquiv :
    leftSection k r R 1 ≃* leftSubgroup (k + 1) r R :=
  restrictEquiv (rankCast (show k + 1 + r = k + r + 1 by omega)).symm _ _
    (mem_leftSection_one_iff k r)

/-- The actual right cyclic section, in lower right mixed-product coordinates. -/
def rightCycleSectionEquiv :
    rightSection k r R 0 ≃* rightSubgroup (k + 1) r R :=
  restrictEquiv (rankCast (show k + 1 + r = k + r + 1 by omega)).symm _ _
    (mem_rightSection_zero_iff k r)

/-- The actual right identity section, in lower left mixed-product coordinates. -/
def rightIdentitySectionEquiv :
    rightSection k r R 1 ≃* leftSubgroup (r + 1) k R :=
  restrictEquiv (rankCast (show r + 1 + k = k + r + 1 by omega)).symm _ _
    (mem_rightSection_one_iff k r)

@[simp] theorem leftIdentitySectionEquiv_val (g : leftSection k r R 1) :
    (leftIdentitySectionEquiv k r R g).val =
      (rankCast (show k + 1 + r = k + r + 1 by omega)).symm g.val := rfl

@[simp] theorem rightCycleSectionEquiv_val (g : rightSection k r R 0) :
    (rightCycleSectionEquiv k r R g).val =
      (rankCast (show k + 1 + r = k + r + 1 by omega)).symm g.val := rfl

@[simp] theorem rightIdentitySectionEquiv_val (g : rightSection k r R 1) :
    (rightIdentitySectionEquiv k r R g).val =
      (rankCast (show r + 1 + k = k + r + 1 by omega)).symm g.val := rfl

variable [TopologicalSpace R]

theorem continuous_leftIdentitySectionEquiv :
    Continuous (leftIdentitySectionEquiv k r R) :=
  ((continuous_rankCast_symm _).comp continuous_subtype_val).subtype_mk _

theorem continuous_leftIdentitySectionEquiv_symm :
    Continuous (leftIdentitySectionEquiv k r R).symm :=
  ((continuous_rankCast (show k + 1 + r = k + r + 1 by omega)).comp
    continuous_subtype_val).subtype_mk _

theorem continuous_rightCycleSectionEquiv :
    Continuous (rightCycleSectionEquiv k r R) :=
  ((continuous_rankCast_symm _).comp continuous_subtype_val).subtype_mk _

theorem continuous_rightCycleSectionEquiv_symm :
    Continuous (rightCycleSectionEquiv k r R).symm :=
  ((continuous_rankCast (show k + 1 + r = k + r + 1 by omega)).comp
    continuous_subtype_val).subtype_mk _

theorem continuous_rightIdentitySectionEquiv :
    Continuous (rightIdentitySectionEquiv k r R) :=
  ((continuous_rankCast_symm _).comp continuous_subtype_val).subtype_mk _

theorem continuous_rightIdentitySectionEquiv_symm :
    Continuous (rightIdentitySectionEquiv k r R).symm :=
  ((continuous_rankCast (show r + 1 + k = k + r + 1 by omega)).comp
    continuous_subtype_val).subtype_mk _

end Equivalences

end Langlands.GeneralLinear.Mirabolic.MixedOrbit
