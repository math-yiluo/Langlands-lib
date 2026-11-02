import Mathlib.Analysis.Normed.Field.Approximation
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # An explicit coefficient neighborhood with distinct real roots -/

noncomputable section

namespace Langlands.Global.FieldRealization

open Polynomial
open scoped BigOperators ComplexConjugate

/-- A monic polynomial with the distinct real roots `0, ..., n-1`. -/
def realRootModel (n : ℕ) : Polynomial ℝ :=
  ∏ i : Fin n, (X - C (i.val : ℝ))

theorem realRootModel_monic (n : ℕ) : (realRootModel n).Monic :=
  monic_prod_X_sub_C _ _

theorem realRootModel_natDegree (n : ℕ) : (realRootModel n).natDegree = n := by
  unfold realRootModel
  rw [natDegree_prod_of_monic
    (h := fun (i : Fin n) _ => monic_X_sub_C (i.val : ℝ))]
  simp only [natDegree_X_sub_C, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, mul_one]

theorem realRootModel_aeval (n : ℕ) (i : Fin n) :
    aeval (i.val : ℂ) (realRootModel n) = 0 := by
  simp only [realRootModel, map_prod, map_sub, aeval_X, aeval_C]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)

/-- A uniform positive coefficient radius around `realRootModel n`. -/
def realRootRadius (n : ℕ) : ℝ :=
  (1 / (4 * (n + 1 : ℝ))) ^ n / (n + 1 : ℝ)

theorem realRootRadius_pos (n : ℕ) : 0 < realRootRadius n := by
  unfold realRootRadius
  positivity

private theorem one_le_norm_natCast_sub {i j : ℕ} (hne : i ≠ j) :
    1 ≤ ‖(i : ℂ) - (j : ℂ)‖ := by
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_natCast,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rcases lt_or_gt_of_ne hne with h | h
  · have hij : (i : ℝ) ≤ j := by exact_mod_cast h.le
    rw [abs_of_nonpos (sub_nonpos.mpr hij)]
    have h' : (i : ℝ) + 1 ≤ j := by exact_mod_cast h
    linarith
  · have hji : (j : ℝ) ≤ i := by exact_mod_cast h.le
    rw [abs_of_nonneg (sub_nonneg.mpr hji)]
    have h' : (j : ℝ) + 1 ≤ i := by exact_mod_cast h
    linarith

private theorem realRootRadius_bound {n : ℕ} (hn : n ≠ 0) (i : Fin n) :
    ((n + 1 : ℝ) * realRootRadius n) ^ (n : ℝ)⁻¹ *
      max ‖(i.val : ℂ)‖ 1 < 1 / 2 := by
  have hn1 : (n + 1 : ℝ) ≠ 0 := by positivity
  have hq : 0 ≤ 1 / (4 * (n + 1 : ℝ)) := by positivity
  unfold realRootRadius
  rw [mul_div_cancel₀ _ hn1, Real.pow_rpow_inv_natCast hq hn, Complex.norm_natCast]
  have hi : max (i.val : ℝ) 1 ≤ n + 1 := by
    apply max_le
    · exact_mod_cast Nat.le_succ_of_le (Nat.le_of_lt i.isLt)
    · have : (0 : ℝ) ≤ n := by positivity
      linarith
  calc
    _ ≤ (1 / (4 * (n + 1 : ℝ))) * (n + 1 : ℝ) :=
      mul_le_mul_of_nonneg_left hi hq
    _ = 1 / 4 := by field_simp
    _ < 1 / 2 := by norm_num

/-- Sufficiently small coefficient changes of a monic polynomial around the
model with natural-number roots preserve splitting over the reals and
separability. -/
theorem splits_separable_of_coeff_lt_realRootRadius (n : ℕ)
    (g : Polynomial ℝ) (hgm : g.Monic) (hdeg : g.natDegree = n)
    (hcoeff : ∀ k : ℕ, ‖g.coeff k - (realRootModel n).coeff k‖ < realRootRadius n) :
    g.Splits ∧ g.Separable := by
  classical
  by_cases hn : n = 0
  · have hg1 : g = 1 := hgm.natDegree_eq_zero.mp (hdeg.trans hn)
    simp [hg1]
  have hex : ∀ i : Fin n, ∃ z : ℂ, aeval z g = 0 ∧ ‖(i.val : ℂ) - z‖ < 1 / 2 := by
    intro i
    obtain ⟨z, hz, hclose⟩ :=
      Polynomial.exists_aroots_norm_sub_lt_of_norm_coeff_sub_lt
        (realRootRadius_pos n) (realRootModel_aeval n i) (realRootModel_monic n)
        hgm (hdeg.trans (realRootModel_natDegree n).symm) hcoeff (IsAlgClosed.splits _)
    refine ⟨z, (Polynomial.mem_aroots.mp hz).2, ?_⟩
    rw [realRootModel_natDegree] at hclose
    exact hclose.trans (realRootRadius_bound hn i)
  choose z hz hclose using hex
  have center_unique : ∀ (i j : Fin n) (w : ℂ),
      ‖(i.val : ℂ) - w‖ < 1 / 2 → ‖(j.val : ℂ) - w‖ < 1 / 2 → i = j := by
    intro i j w hi hj
    by_contra hne
    have hsep := one_le_norm_natCast_sub (mt Fin.ext hne)
    have htri : ‖(i.val : ℂ) - (j.val : ℂ)‖ ≤
        ‖(i.val : ℂ) - w‖ + ‖(j.val : ℂ) - w‖ := by
      simpa only [norm_sub_rev] using
        norm_sub_le_norm_sub_add_norm_sub (i.val : ℂ) w (j.val : ℂ)
    linarith
  have hinj : Function.Injective z := by
    intro i j hij
    exact center_unique i j (z i) (hclose i) (hij ▸ hclose j)
  let S : Finset ℂ := Finset.univ.image z
  have hS : S.card = n := by
    simpa [S] using Finset.card_image_of_injective Finset.univ hinj
  have hrootseq : (g.map (algebraMap ℝ ℂ)).roots = S.val := by
    apply Polynomial.roots_eq_of_natDegree_le_card_of_ne_zero
    · intro w hw
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hw
      rw [eval_map_algebraMap]
      exact hz i
    · simp [hdeg, hS]
    · exact (hgm.map _).ne_zero
  have hreal : ∀ i : Fin n, (z i).im = 0 := by
    intro i
    have hconj : conj (z i) ∈ (g.map (algebraMap ℝ ℂ)).roots := by
      apply ((g.map _).mem_roots (hgm.map _).ne_zero).mpr
      rw [IsRoot.def, eval_map_algebraMap]
      rw [Polynomial.aeval_conj, hz i, map_zero]
    rw [hrootseq] at hconj
    change conj (z i) ∈ S at hconj
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hconj
    have hci : ‖(i.val : ℂ) - conj (z i)‖ < 1 / 2 := by
      have heq : (i.val : ℂ) - conj (z i) = conj ((i.val : ℂ) - z i) := by
        rw [map_sub, map_natCast]
      rw [heq, Complex.norm_conj]
      exact hclose i
    have hij : i = j := center_unique i j (conj (z i)) hci (hj ▸ hclose j)
    exact Complex.conj_eq_iff_im.mp (hj.symm.trans (congrArg z hij.symm))
  have hs : (g.map (algebraMap ℝ ℂ)).Splits := IsAlgClosed.splits _
  constructor
  · apply hs.of_splits_map_of_injective (algebraMap ℝ ℂ).injective
    intro w hw
    rw [hrootseq] at hw
    change w ∈ S at hw
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hw
    refine ⟨(z i).re, ?_⟩
    exact Complex.ext rfl (by simpa using (hreal i).symm)
  · apply (Polynomial.separable_map (algebraMap ℝ ℂ)).mp
    apply (Polynomial.nodup_roots_iff_of_splits (hgm.map _).ne_zero hs).mp
    rw [hrootseq]
    exact S.nodup

end Langlands.Global.FieldRealization
