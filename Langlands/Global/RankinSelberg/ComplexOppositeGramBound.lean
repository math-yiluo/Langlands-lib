import Langlands.Representation.Archimedean.ComplexStandardNontrivialProof
import Langlands.Representation.RankinSelberg.FiniteCauchyBinet

/-!
# Tail Gram determinants control the complex opposite-cell coordinates

For a lower-unipotent matrix, each tail Gram determinant contains the unit
principal minor. The minor obtained by replacing the first tail column by
an earlier column has determinant equal to the corresponding strictly lower
entry. The product of the tail Gram determinants thus controls all entries.
-/

noncomputable section

open Finset
open scoped Classical Matrix Matrix.Norms.Elementwise

namespace Langlands.Global.RankinSelbergGlobal.ComplexOppositeGramBound

open Langlands.Archimedean (LowIdx lowGram lowMinor)
open GeneralLinear (upperUnipotent)
open Langlands.GeneralLinear.Spherical (det_rectangular_mul)

variable {n : ℕ}
local notation "N" => upperUnipotent n ℂ
local notation "M" => Matrix (Fin n) (Fin n) ℂ

private def tailOrder (n k : ℕ) : Fin (Fintype.card (LowIdx n k)) ≃o LowIdx n k :=
  Fintype.orderIsoFinOfCardEq _ rfl

private abbrev Columns (n k : ℕ) := {s : Finset (Fin n) // s.card = Fintype.card (LowIdx n k)}

private def tailGramTerm (A : M) (k : ℕ) (s : Columns n k) : ℝ :=
  Complex.normSq (A.submatrix (Subtype.val ∘ tailOrder n k) (s.val.orderEmbOfFin s.2)).det

private theorem lowGram_re_eq_sum (A : M) (k : ℕ) :
    (lowGram k A).re = ∑ s : Columns n k, tailGramTerm A k s := by
  let e := tailOrder n k
  let T := A.submatrix (Subtype.val : LowIdx n k → Fin n) id
  let B := T.submatrix e id
  have hBB : B * Bᴴ = (T * Tᴴ).submatrix e e := by
    ext i j
    simp [B, Matrix.mul_apply]
  have hdet : (B * Bᴴ).det = lowGram k A := by
    rw [hBB]
    exact Matrix.det_submatrix_equiv_self e.toEquiv (T * Tᴴ)
  rw [← hdet, det_rectangular_mul, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro s _
  have hconj : Bᴴ.submatrix (s.val.orderEmbOfFin s.2) id = (B.submatrix id (s.val.orderEmbOfFin s.2))ᴴ := rfl
  rw [hconj, Matrix.det_conjTranspose, Complex.star_def, Complex.mul_conj, Complex.ofReal_re]
  rfl

private def selectedColumns {k : ℕ} (c : LowIdx n k ↪o Fin n) : Columns n k :=
  ⟨univ.map ((tailOrder n k).toOrderEmbedding.trans c).toEmbedding, by simp⟩

private theorem mem_selectedColumns {k : ℕ} (c : LowIdx n k ↪o Fin n) (j : Fin n) :
    j ∈ (selectedColumns c).val ↔ j ∈ Set.range c := by
  change j ∈ univ.map ((tailOrder n k).toOrderEmbedding.trans c).toEmbedding ↔ _
  simp only [mem_map, mem_univ, true_and]
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨tailOrder n k q, rfl⟩
  · rintro ⟨q, rfl⟩
    exact ⟨(tailOrder n k).symm q, by simp⟩

private theorem tailGramTerm_selected {k : ℕ} (A : M) (c : LowIdx n k ↪o Fin n) :
    tailGramTerm A k (selectedColumns c) = Complex.normSq (A.submatrix Subtype.val c).det := by
  let e := tailOrder n k
  have hc : (selectedColumns c).val.orderEmbOfFin (selectedColumns c).2 = e.toOrderEmbedding.trans c := by
    symm
    exact Finset.orderEmbOfFin_unique' _ fun q =>
      (mem_selectedColumns c _).mpr ⟨e q, rfl⟩
  rw [tailGramTerm, hc]
  change Complex.normSq (((A.submatrix Subtype.val c).submatrix e e).det) = _
  exact congrArg Complex.normSq (Matrix.det_submatrix_equiv_self e.toEquiv (A.submatrix Subtype.val c))

private def principalColumns (n k : ℕ) : LowIdx n k ↪o Fin n := OrderEmbedding.subtype _

private def replacementColumns {i j : Fin n} (hji : j < i) : LowIdx n i.val ↪o Fin n :=
  OrderEmbedding.ofStrictMono (fun a => if a.val = i then j else a.val) (by
    intro a b hab
    have ha : i ≤ a.val := a.2
    have hb : i < b.val := ha.trans_lt hab
    by_cases h : a.val = i
    · simpa only [ite_eq_left h, ite_eq_right hb.ne'] using hji.trans hb
    · simpa only [ite_eq_right h, ite_eq_right hb.ne'] using (show a.val < b.val from hab))

private theorem replacementColumns_apply {i j : Fin n} (hji : j < i) (a : LowIdx n i.val) :
    replacementColumns hji a = if a.val = i then j else a.val := rfl

private theorem transpose_lower (u : N) : u.val.valᵀ.IsLowerTriangular :=
  fun _ _ h => GeneralLinear.UpperUnipotent.entry_eq_zero u h

/-- Every bottom-right principal minor of the transpose of an upper-unipotent matrix is one. -/
theorem lowMinor_transpose_unipotent (u : N) (k : ℕ) : lowMinor k u.val.valᵀ = 1 := by
  rw [lowMinor, Matrix.det_of_isLowerTriangular]
  · exact Finset.prod_eq_one fun i _ => GeneralLinear.UpperUnipotent.entry_diag u i.val
  · intro a b hab
    exact transpose_lower u hab

private theorem replacement_det (u : N) {i j : Fin n} (hji : j < i) :
    (u.val.valᵀ.submatrix Subtype.val (replacementColumns hji)).det = u.val.val j i := by
  let first : LowIdx n i.val := ⟨i, le_rfl⟩
  rw [Matrix.det_of_isLowerTriangular]
  · rw [Finset.prod_eq_single_of_mem first (Finset.mem_univ _) (fun a _ ha => ?_)]
    · simp [Matrix.submatrix_apply, replacementColumns_apply, first]
    · rw [Matrix.submatrix_apply, replacementColumns_apply,
        ite_eq_right (fun h => ha (Subtype.ext h))]
      exact GeneralLinear.UpperUnipotent.entry_diag u a.val
  · intro a b hab
    have hi : i ≤ a.val := a.2
    have hb : b.val ≠ i := (hi.trans_lt hab).ne'
    rw [Matrix.submatrix_apply, replacementColumns_apply, ite_eq_right hb]
    exact transpose_lower u hab

/-- Each tail Gram determinant is at least one on the opposite cell. -/
theorem one_le_lowGram_transpose (u : N) (k : ℕ) : 1 ≤ (lowGram k u.val.valᵀ).re := by
  let c := selectedColumns (principalColumns n k)
  have h : tailGramTerm u.val.valᵀ k c = 1 := by
    rw [tailGramTerm_selected]
    change Complex.normSq (lowMinor k u.val.valᵀ) = 1
    rw [lowMinor_transpose_unipotent, map_one]
  rw [lowGram_re_eq_sum, ← h]
  exact Finset.single_le_sum (f := tailGramTerm u.val.valᵀ k)
    (fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ c)

/-- A strict upper entry and the unit principal minor give two distinct summands of the Gram
identity on the transposed matrix. -/
theorem one_add_sq_entry_le_lowGram (u : N) {i j : Fin n} (hji : j < i) :
    1 + ‖u.val.val j i‖ ^ 2 ≤ (lowGram i.val u.val.valᵀ).re := by
  let c := selectedColumns (principalColumns n i.val)
  let d := selectedColumns (replacementColumns hji)
  have hc : tailGramTerm u.val.valᵀ i.val c = 1 := by
    rw [tailGramTerm_selected]
    change Complex.normSq (lowMinor i.val u.val.valᵀ) = 1
    rw [lowMinor_transpose_unipotent, map_one]
  have hd : tailGramTerm u.val.valᵀ i.val d = ‖u.val.val j i‖ ^ 2 := by
    rw [tailGramTerm_selected, replacement_det, Complex.normSq_eq_norm_sq]
  have hdc : d ≠ c := by
    intro h
    have hjd : j ∈ d.val := (mem_selectedColumns _ _).mpr ⟨⟨i, le_rfl⟩, by simp [replacementColumns_apply]⟩
    rw [h] at hjd
    obtain ⟨a, ha⟩ := (mem_selectedColumns _ _).mp hjd
    have hi : i ≤ a.val := a.2
    change a.val = j at ha
    exact hji.not_ge (ha ▸ hi)
  rw [lowGram_re_eq_sum, ← hc, ← hd]
  calc
    _ ≤ tailGramTerm u.val.valᵀ i.val c +
        ∑ s ∈ univ.erase c, tailGramTerm u.val.valᵀ i.val s :=
      add_le_add le_rfl (Finset.single_le_sum (f := tailGramTerm u.val.valᵀ i.val)
        (fun _ _ => Complex.normSq_nonneg _) (Finset.mem_erase.mpr ⟨hdc, Finset.mem_univ _⟩))
    _ = _ := Finset.add_sum_erase _ _ (Finset.mem_univ _)

/-- The Gram product over all tail rows of the transpose of an upper-unipotent matrix. -/
def oppositeGramProduct (u : N) : ℝ := ∏ i : Fin n, (lowGram i.val u.val.valᵀ).re

theorem one_le_oppositeGramProduct (u : N) : 1 ≤ oppositeGramProduct u :=
  Finset.one_le_prod₀ fun i _ => one_le_lowGram_transpose u i.val

/-- The Gram product controls the square of the largest entrywise displacement from one. -/
def ComplexOppositeGramBoundStatement : Prop :=
  ∀ (n : ℕ) (u : upperUnipotent n ℂ), 1 + ‖u.val.val - 1‖ ^ 2 ≤ oppositeGramProduct u

theorem complexOppositeGramBound : ComplexOppositeGramBoundStatement := by
  intro n u
  have hnonneg : 0 ≤ oppositeGramProduct u - 1 := sub_nonneg.mpr (one_le_oppositeGramProduct u)
  have hsqrt : ‖u.val.val - 1‖ ≤ Real.sqrt (oppositeGramProduct u - 1) := by
    apply (Matrix.norm_le_iff (Real.sqrt_nonneg _)).mpr
    intro i j
    rw [Matrix.sub_apply]
    rcases lt_trichotomy i j with hij | rfl | hji
    · rw [Matrix.one_apply_ne hij.ne, sub_zero, Real.le_sqrt (norm_nonneg _) hnonneg]
      have hle : (lowGram j.val u.val.valᵀ).re ≤ oppositeGramProduct u := by
        simpa only [oppositeGramProduct, max_eq_left (one_le_lowGram_transpose u _)] using
          Finset.le_prod_max_one (Finset.mem_univ j) (fun k : Fin n => (lowGram k.val u.val.valᵀ).re)
      linarith [(one_add_sq_entry_le_lowGram u hij).trans hle]
    · rw [GeneralLinear.UpperUnipotent.entry_diag, Matrix.one_apply_eq, sub_self, norm_zero]
      positivity
    · rw [GeneralLinear.UpperUnipotent.entry_eq_zero u hji, Matrix.one_apply_ne hji.ne', sub_zero, norm_zero]
      positivity
  linarith [(Real.le_sqrt (norm_nonneg _) hnonneg).mp hsqrt]

end Langlands.Global.RankinSelbergGlobal.ComplexOppositeGramBound
