import Langlands.AllFieldBZ.Group.GL.MirabolicMixedOrbitData
import Langlands.Group.GL.MirabolicMixedOrbitSections

/-!
# All-field port of `Langlands.Group.GL.MirabolicMixedOrbitSections`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Group.GL.MirabolicMixedOrbitSections` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ.GeneralLinear.Mirabolic.MixedOrbit
open Langlands.GeneralLinear.Mirabolic.MixedOrbit hiding isTopologicalRing_of_topologicalData
open Langlands.GeneralLinear.Mirabolic.MixedProduct hiding leftSection rightSection
universe u

section EntryCriteria
variable {R : Type u} [CommRing R] {k r : ℕ}

private theorem _root_.Langlands.GeneralLinear.Mirabolic.MixedOrbit.mem_leftSubgroup_iff_bounds (g : Langlands.GeneralLinear.mirabolic (k + r) R) :
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

private theorem _root_.Langlands.GeneralLinear.Mirabolic.MixedOrbit.mem_rightSubgroup_iff_bounds (g : Langlands.GeneralLinear.mirabolic (k + r) R) :
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

private theorem _root_.Langlands.GeneralLinear.Mirabolic.MixedOrbit.rankCast_mem_left_iff {n : ℕ} (h : k + r = n) (g : Langlands.GeneralLinear.mirabolic n R) :
    (rankCast h).symm g ∈ leftSubgroup k r R ↔
      ∀ i j : Fin (n + 1), k ≤ i.val → j.val < k → g.val.val i j = 0 := by
  subst h
  rw [mem_leftSubgroup_iff_bounds]
  rfl

private theorem _root_.Langlands.GeneralLinear.Mirabolic.MixedOrbit.rankCast_mem_right_iff {n : ℕ} (h : k + r = n) (g : Langlands.GeneralLinear.mirabolic n R) :
    (rankCast h).symm g ∈ rightSubgroup k r R ↔
      ∀ i j : Fin (n + 1), r ≤ i.val → i.val < r + k →
        (j.val < r ∨ j = Fin.last n) → g.val.val i j = 0 := by
  subst h
  rw [mem_rightSubgroup_iff_bounds]
  rfl

end EntryCriteria
section IdentitySections
variable {R : Type u} [CommRing R] (k r : ℕ)

end IdentitySections
section RightCycleSection
variable {R : Type u} [CommRing R] (k r : ℕ)

private theorem _root_.Langlands.GeneralLinear.Mirabolic.MixedOrbit.cycle_inv_conjugate_entry {t a : ℕ} (ha : a ≤ t)
    (g : Langlands.GeneralLinear.mirabolic (t + 1) R) (i j : Fin (t + 2)) :
    ((cycleElement t a ha R)⁻¹ * g * cycleElement t a ha R).val.val i j =
      g.val.val (descendingCycle t a ha i) (descendingCycle t a ha j) := by
  change ((Langlands.GeneralLinear.permutation (t + 2) R (descendingCycle t a ha))⁻¹ * g.val *
    Langlands.GeneralLinear.permutation (t + 2) R (descendingCycle t a ha)).val i j = _
  rw [Langlands.GeneralLinear.mul_permutation_entry, Langlands.GeneralLinear.permutation_inv, Langlands.GeneralLinear.permutation_mul_entry]
  rfl

private theorem _root_.Langlands.GeneralLinear.Mirabolic.MixedOrbit.rightCycle_middle (i : Fin (k + r + 3))
    (hi : r < i.val) (hi' : i.val ≤ k + r + 1) :
    descendingCycle (k + r + 1) r (by omega) i =
      (⟨i.val - 1, by omega⟩ : Fin (k + r + 2)).castSucc := by
  apply Fin.ext
  change (if i.val = r then _ else if r < i.val ∧ i.val ≤ k + r + 1 then _ else _) = _
  rw [ite_eq_right (by omega), ite_eq_left ⟨hi, hi'⟩]
  rfl

private theorem _root_.Langlands.GeneralLinear.Mirabolic.MixedOrbit.rightCycle_first (j : Fin (k + r + 3)) (hj : j.val < r) :
    descendingCycle (k + r + 1) r (by omega) j =
      (⟨j.val, by omega⟩ : Fin (k + r + 2)).castSucc := by
  apply Fin.ext
  change (if j.val = r then _ else if r < j.val ∧ j.val ≤ k + r + 1 then _ else _) = _
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  rfl

private theorem _root_.Langlands.GeneralLinear.Mirabolic.MixedOrbit.rightCycle_start (j : Fin (k + r + 3)) (hj : j.val = r) :
    descendingCycle (k + r + 1) r (by omega) j =
      (Fin.last (k + r + 1)).castSucc := by
  apply Fin.ext
  change (if j.val = r then _ else _) = _
  rw [ite_eq_left hj]
  rfl

end RightCycleSection
section Equivalences
private def _root_.Langlands.GeneralLinear.Mirabolic.MixedOrbit.restrictEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (A : Subgroup G) (B : Subgroup H) (h : ∀ g, g ∈ A ↔ e g ∈ B) : A ≃* B where
  toFun g := ⟨e g.val, (h g.val).mp g.property⟩
  invFun g := ⟨e.symm g.val, (h _).mpr (by
    simpa only [e.apply_symm_apply] using g.property)⟩
  left_inv g := Subtype.ext (e.symm_apply_apply g.val)
  right_inv g := Subtype.ext (e.apply_symm_apply g.val)
  map_mul' g g' := Subtype.ext (e.map_mul g.val g'.val)

variable (k r : ℕ) (R : Type u) [CommRing R]

variable [TopologicalSpace R]

end Equivalences
end Langlands.AllFieldBZ.GeneralLinear.Mirabolic.MixedOrbit
