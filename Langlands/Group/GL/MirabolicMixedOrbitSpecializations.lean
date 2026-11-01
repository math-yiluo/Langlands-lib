import Langlands.Group.GL.MirabolicMixedOrbitCoverageStatement

/-!
# Entrywise specializations for the two mixed mirabolic subgroups

These elementary matrix lemmas connect the published rank-transported mixed
subgroups with the upper-left block conditions used in the orbit proof.
They prove no orbit coverage or ordering statement.
-/

namespace Langlands.GeneralLinear.Mirabolic.MixedOrbit

open Langlands.GeneralLinear.Mirabolic.MixedProduct

universe u

variable {R : Type u} [CommRing R]

theorem mem_leftInducing_iff_lowerLeft (k r : ℕ) (g : mirabolic (k + r + 2) R) :
    g ∈ leftInducing k r R ↔
      ∀ i j : Fin (k + r + 3), k < i.val → j.val ≤ k → g.val.val i j = 0 := by
  rw [mem_leftInducing_iff, mem_leftSubgroup_iff_entry]
  constructor
  · intro h i j hi hj
    let a : Fin (r + 1 + 1) := ⟨i.val - (k + 1), by omega⟩
    let b : Fin (k + 1) := ⟨j.val, by omega⟩
    have he := h a b
    rw [rankCast_symm_apply] at he
    have ha : Fin.cast (congrArg (· + 1) (totalRank_eq k r))
        (leftIndex (k + 1) (r + 1) (Sum.inr a)) = i := by
      apply Fin.ext
      simp only [Fin.val_cast, leftIndex_inr_val]
      dsimp [a]
      omega
    have hb : Fin.cast (congrArg (· + 1) (totalRank_eq k r))
        (leftIndex (k + 1) (r + 1) (Sum.inl b)) = j := by
      apply Fin.ext
      simp only [Fin.val_cast, leftIndex_inl_val]
      rfl
    simpa only [ha, hb] using he
  · intro h a b
    rw [rankCast_symm_apply]
    apply h
    · simp only [Fin.val_cast, leftIndex_inr_val]
      omega
    · simp only [Fin.val_cast, leftIndex_inl_val]
      omega

theorem leftInducing_projection_upperHead (k r : ℕ)
    (g : mirabolic (k + r + 2) R) (hg : g ∈ leftInducing k r R)
    (i j : Fin (k + r + 2)) (hi : k < i.val) (hj : j.val ≤ k) :
    (projection g).val i j = 0 :=
  (mem_leftInducing_iff_lowerLeft k r g).mp hg i.castSucc j.castSucc hi hj

theorem levi_mem_leftInducing (k r : ℕ) (A : Langlands.GeneralLinear (k + r + 2) R)
    (hA : ∀ i j : Fin (k + r + 2), k < i.val → j.val ≤ k → A.val i j = 0) :
    levi A ∈ leftInducing k r R := by
  rw [mem_leftInducing_iff_lowerLeft]
  intro i j hi hj
  revert hi
  let b : Fin (k + r + 2) := ⟨j.val, by omega⟩
  have hb : b.castSucc = j := Fin.ext rfl
  rw [← hb]
  refine Fin.lastCases ?_ (fun a => ?_) i
  · intro _
    rw [levi_bottom]
    simp only [Fin.castSucc_ne_last, ↓reduceIte]
  · intro hi
    rw [levi_first]
    exact hA a b hi hj

theorem rightInducing_projection_upperHead (k r : ℕ)
    (g : mirabolic (k + r + 2) R) (hg : g ∈ rightInducing k r R)
    (i j : Fin (k + r + 2)) (hi : r < i.val) (hj : j.val ≤ r) :
    (projection g).val i j = 0 := by
  have h := (mem_rightSubgroup_iff_entry
    ((rankCast (totalRank_eq k r)).symm g)).mp hg
  let a : Fin (k + 1) := ⟨i.val - (r + 1), by omega⟩
  let b : Fin (r + 1) := ⟨j.val, by omega⟩
  have he := h a b.castSucc
  rw [rankCast_symm_apply] at he
  have ha : Fin.cast (congrArg (· + 1) (totalRank_eq k r))
      (rightIndex (k + 1) (r + 1) (Sum.inr a)) = i.castSucc := by
    apply Fin.ext
    simp only [Fin.val_cast, rightIndex_middle_val, Fin.val_castSucc]
    dsimp [a]
    omega
  have hb : Fin.cast (congrArg (· + 1) (totalRank_eq k r))
      (rightIndex (k + 1) (r + 1) (Sum.inl b.castSucc)) = j.castSucc := by
    apply Fin.ext
    simp only [Fin.val_cast, rightIndex_first_val, Fin.val_castSucc]
    rfl
  simpa only [ha, hb, projection_apply] using he

theorem levi_mem_rightInducing (k r : ℕ) (A : Langlands.GeneralLinear (k + r + 2) R)
    (hA : ∀ i j : Fin (k + r + 2), r < i.val → j.val ≤ r → A.val i j = 0) :
    levi A ∈ rightInducing k r R := by
  rw [mem_rightInducing_iff, mem_rightSubgroup_iff_entry]
  intro i j
  rw [rankCast_symm_apply]
  let a : Fin (k + r + 2) := ⟨r + 1 + i.val, by omega⟩
  have ha : Fin.cast (congrArg (· + 1) (totalRank_eq k r))
      (rightIndex (k + 1) (r + 1) (Sum.inr i)) = a.castSucc := by
    apply Fin.ext
    simp only [Fin.val_cast, rightIndex_middle_val, Fin.val_castSucc]
    rfl
  rw [ha]
  refine Fin.lastCases ?_ (fun b => ?_) j
  · have hb : Fin.cast (congrArg (· + 1) (totalRank_eq k r))
        (rightIndex (k + 1) (r + 1) (Sum.inl (Fin.last (r + 1)))) =
        Fin.last (k + r + 2) := by
      apply Fin.ext
      simp only [Fin.val_cast, rightIndex_last, Fin.val_last]
      omega
    rw [hb, levi_last]
  · let c : Fin (k + r + 2) := ⟨b.val, by omega⟩
    have hb : Fin.cast (congrArg (· + 1) (totalRank_eq k r))
        (rightIndex (k + 1) (r + 1) (Sum.inl b.castSucc)) = c.castSucc := by
      apply Fin.ext
      simp only [Fin.val_cast, rightIndex_first_val, Fin.val_castSucc]
      rfl
    rw [hb, levi_first]
    apply hA
    · dsimp [a]
      omega
    · dsimp [c]
      omega

theorem cycleElement_projection_lastRow (t a : ℕ) (ha : a ≤ t) (j : Fin (t + 1)) :
    (projection (cycleElement t a ha R)).val (Fin.last t) j =
      if j.val = a then 1 else 0 := by
  rw [projection_apply, cycleElement_entry]
  have he : descendingCycle t a ha j.castSucc = (Fin.last t).castSucc ↔ j.val = a := by
    rw [Fin.ext_iff, descendingCycle_apply_val]
    simp only [Fin.val_castSucc, Fin.val_last]
    split_ifs <;> omega
  simp only [he]

theorem leftCycleElement_projection_lastRow (k r : ℕ) (j : Fin (k + r + 2)) :
    (projection (leftCycleElement k r R)).val (Fin.last (k + r + 1)) j =
      if j.val = k then 1 else 0 :=
  cycleElement_projection_lastRow (k + r + 1) k (by omega) j

theorem rightCycleElement_projection_lastRow (k r : ℕ) (j : Fin (k + r + 2)) :
    (projection (rightCycleElement k r R)).val (Fin.last (k + r + 1)) j =
      if j.val = r then 1 else 0 :=
  cycleElement_projection_lastRow (k + r + 1) r (by omega) j

end Langlands.GeneralLinear.Mirabolic.MixedOrbit
