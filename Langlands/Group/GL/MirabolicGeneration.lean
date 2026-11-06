import Langlands.Group.GL.Mirabolic
import Langlands.Group.GL.Maps
import Langlands.Group.GL.Transvection

/-! # Generation by the mirabolic and its inverse-transpose image -/

namespace Langlands.GeneralLinear

universe uF

section Ring

variable {F : Type uF} [CommRing F] {n : ℕ}

private theorem lastColumn_mul (g h : GeneralLinear (n + 1) F)
    (hh : ∀ i, h.val i (Fin.last n) = if i = Fin.last n then 1 else 0)
    (i : Fin (n + 1)) :
    (g * h).val i (Fin.last n) = g.val i (Fin.last n) := by
  change (g.val * h.val) i (Fin.last n) = _
  simp [Matrix.mul_apply, hh]

/-- The subgroup fixing the last standard column vector. -/
def oppositeMirabolic (n : ℕ) (F : Type uF) [CommRing F] :
    Subgroup (GeneralLinear (n + 1) F) where
  carrier := {g | ∀ i, g.val i (Fin.last n) = if i = Fin.last n then 1 else 0}
  one_mem' := by intro i; simp [Matrix.one_apply]
  mul_mem' := by
    intro g h hg hh i
    rw [lastColumn_mul g h hh i, hg i]
  inv_mem' := by
    intro g hg i
    have h := lastColumn_mul g⁻¹ g hg i
    rw [inv_mul_cancel] at h
    simpa [Matrix.one_apply] using h.symm

@[simp] theorem mem_oppositeMirabolic (g : GeneralLinear (n + 1) F) :
    g ∈ oppositeMirabolic n F ↔
      ∀ i, g.val i (Fin.last n) = if i = Fin.last n then 1 else 0 := Iff.rfl

@[simp] theorem inverseTranspose_mem_oppositeMirabolic_iff
    (g : GeneralLinear (n + 1) F) :
    inverseTranspose (n + 1) F g ∈ oppositeMirabolic n F ↔ g ∈ mirabolic n F := by
  change (g⁻¹ ∈ mirabolic n F) ↔ g ∈ mirabolic n F
  exact (mirabolic n F).inv_mem_iff

/-- Inverse transpose carries the last-row mirabolic onto the last-column one. -/
theorem mirabolic_map_inverseTranspose :
    (mirabolic n F).map (inverseTranspose (n + 1) F).toMonoidHom =
      oppositeMirabolic n F := by
  ext g
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact inverseTranspose_mem_oppositeMirabolic_iff h |>.mpr hh
  · intro hg
    refine ⟨inverseTranspose (n + 1) F g, ?_, by simp⟩
    apply (inverseTranspose_mem_oppositeMirabolic_iff _).mp
    simpa using hg

end Ring

section Field

variable {F : Type uF} [Field F] {n : ℕ}

private theorem transvection_mem_of_mirabolic_le
    (H : Subgroup (GeneralLinear (n + 1) F))
    (hP : mirabolic n F ≤ H) (hQ : oppositeMirabolic n F ≤ H)
    (i j : Fin (n + 1)) (hij : i ≠ j) (c : F) :
    transvectionUnit i j hij c ∈ H := by
  by_cases hi : i = Fin.last n
  · apply hQ
    have hj : j ≠ Fin.last n := by simpa [hi] using Ne.symm hij
    intro a
    change (Matrix.transvection i j c) a (Fin.last n) = _
    simp [Matrix.transvection, Matrix.one_apply, hj]
  · apply hP
    intro b
    change (Matrix.transvection i j c) (Fin.last n) b = _
    simp [Matrix.transvection, Matrix.one_apply, hi, eq_comm]

private theorem diagonal_mem_of_mirabolic_le
    (hn : 0 < n) (H : Subgroup (GeneralLinear (n + 1) F))
    (hP : mirabolic n F ≤ H) (hQ : oppositeMirabolic n F ≤ H)
    (D : Fin (n + 1) → F) (hd : ∀ i, D i ≠ 0)
    (g : GeneralLinear (n + 1) F) (hg : g.val = Matrix.diagonal D) :
    g ∈ H := by
  let a : Fin (n + 1) := ⟨0, Nat.zero_lt_succ n⟩
  let l : Fin (n + 1) := Fin.last n
  have hal : a ≠ l := by
    intro h
    have := congrArg Fin.val h
    simp only [a, l, Fin.val_last] at this
    omega
  let d := D l
  have hd0 : d ≠ 0 := hd l
  let q₁ := transvectionUnit l a (Ne.symm hal) (1 : F)
  let p := transvectionUnit a l hal (d - 1)
  let q₂ := transvectionUnit l a (Ne.symm hal) (-d⁻¹)
  let b := q₁ * p * q₂
  have hb : b ∈ H :=
    H.mul_mem
      (H.mul_mem (transvection_mem_of_mirabolic_le H hP hQ _ _ _ _)
        (transvection_mem_of_mirabolic_le H hP hQ _ _ _ _))
      (transvection_mem_of_mirabolic_le H hP hQ _ _ _ _)
  have hrow : ∀ j, b.val l j = if j = l then d else 0 := by
    intro j
    change ((Matrix.transvection l a 1 * Matrix.transvection a l (d - 1)) *
      Matrix.transvection l a (-d⁻¹) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) F) l j = _
    by_cases hja : j = a
    · subst j
      rw [Matrix.mul_transvection_apply_same, Matrix.transvection_mul_apply_same,
        Matrix.transvection_mul_apply_same]
      simp [Matrix.transvection, hal, Ne.symm hal]
      field_simp [hd0]
      ring
    · rw [Matrix.mul_transvection_apply_of_ne _ _ l j hja,
        Matrix.transvection_mul_apply_same]
      by_cases hjl : j = l
      · subst j
        simp [Matrix.transvection, hal]
      · simp [Matrix.transvection, Ne.symm hja, hjl, Ne.symm hjl]
  have hgb : ∀ j, g.val l j = b.val l j := by
    intro j
    rw [hrow, hg]
    by_cases hj : j = l
    · subst j; simp [d]
    · simp [hj, Ne.symm hj]
  have hp₀ : g * b⁻¹ ∈ mirabolic n F := by
    intro j
    change (g.val * (b⁻¹).val) l j = _
    have heq : (g.val * (b⁻¹).val) l j = (b.val * (b⁻¹).val) l j := by
      simp only [Matrix.mul_apply, hgb]
    rw [heq]
    change (b * b⁻¹).val l j = _
    simp [l, Matrix.one_apply, eq_comm]
  have h := H.mul_mem (hP hp₀) hb
  simpa only [inv_mul_cancel_right] using h

/-- A subgroup containing the last-row and last-column mirabolics is all of
`GL_(n+1)` once the rank is at least two. -/
theorem eq_top_of_mirabolic_le_of_oppositeMirabolic_le
    (hn : 0 < n) (H : Subgroup (GeneralLinear (n + 1) F))
    (hP : mirabolic n F ≤ H) (hQ : oppositeMirabolic n F ≤ H) : H = ⊤ := by
  apply top_unique
  intro g _
  let P : Matrix (Fin (n + 1)) (Fin (n + 1)) F → Prop :=
    fun A => ∀ u : GeneralLinear (n + 1) F, u.val = A → u ∈ H
  apply Matrix.diagonal_transvection_induction_of_det_ne_zero P g.val g.det_ne_zero
    (hdiag := ?_) (htransvec := ?_) (hmul := ?_) g rfl
  · intro D hD u hu
    have hd : ∀ i, D i ≠ 0 := by
      simpa only [Matrix.det_diagonal, Finset.prod_ne_zero_iff, Finset.mem_univ,
        true_implies] using hD
    exact diagonal_mem_of_mirabolic_le hn H hP hQ D hd u hu
  · intro t u hu
    have he : u = transvectionUnit t.i t.j t.hij t.c := Units.ext hu
    rw [he]
    exact transvection_mem_of_mirabolic_le H hP hQ _ _ _ _
  · intro A B hA hB hPA hPB u hu
    let a := Matrix.GeneralLinearGroup.mkOfDetNeZero A hA
    let b := Matrix.GeneralLinearGroup.mkOfDetNeZero B hB
    have he : u = a * b := Units.ext hu
    rw [he]
    exact H.mul_mem (hPA a rfl) (hPB b rfl)

/-- Subgroup criterion stated directly using inverse-transposed mirabolic elements. -/
theorem eq_top_of_mirabolic_le_of_inverseTranspose_mem
    (hn : 0 < n) (H : Subgroup (GeneralLinear (n + 1) F))
    (hP : mirabolic n F ≤ H)
    (hQ : ∀ g ∈ mirabolic n F, inverseTranspose (n + 1) F g ∈ H) : H = ⊤ := by
  apply eq_top_of_mirabolic_le_of_oppositeMirabolic_le hn H hP
  rw [← mirabolic_map_inverseTranspose]
  rintro _ ⟨g, hg, rfl⟩
  exact hQ g hg

/-- The mirabolic and its inverse-transpose image generate `GL_(n+2)`. -/
theorem mirabolic_sup_inverseTranspose_eq_top (n : ℕ) :
    mirabolic (n + 1) F ⊔
      (mirabolic (n + 1) F).map (inverseTranspose (n + 2) F).toMonoidHom = ⊤ := by
  apply eq_top_of_mirabolic_le_of_inverseTranspose_mem (Nat.zero_lt_succ n) _
    le_sup_left
  intro g hg
  have hle : (mirabolic (n + 1) F).map (inverseTranspose (n + 2) F).toMonoidHom ≤
      mirabolic (n + 1) F ⊔
        (mirabolic (n + 1) F).map (inverseTranspose (n + 2) F).toMonoidHom :=
    le_sup_right
  exact hle (Subgroup.mem_map.mpr ⟨g, hg, rfl⟩)

end Field
end Langlands.GeneralLinear
