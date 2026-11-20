import Langlands.Representation.Archimedean.RealBottomMinorTriangular
import Langlands.Representation.Archimedean.RealCharacterCrossing
import Langlands.Representation.Archimedean.RealBlockPositionData

/-! # Bottom-minor shifts prescribed by increasing position weights -/

noncomputable section

open Finset

namespace Langlands.Archimedean.RealBottomMinorShift

open Langlands.GeneralLinear RealBottomMinorProducts RealBottomMinorTriangular
open RealTiedMinorProduct
open RealCharacterCrossing (PL PL_position)

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

variable {n q : ℕ}

/-- The positions with prescribed weight strictly above the given level. -/
def rowLevel (weights : Fin n → ℕ) (t : Fin q) : Finset (Fin n) :=
  univ.filter fun i => t.val < weights i

/-- The product configuration of the upper level sets. -/
def rows (weights : Fin n → ℕ) : Selection n (fun t : Fin q => (rowLevel weights t).card) :=
  fun t => ⟨rowLevel weights t, rfl⟩

@[simp]
theorem mem_rowLevel (weights : Fin n → ℕ) (t : Fin q) (i : Fin n) :
    i ∈ rowLevel weights t ↔ t.val < weights i := by
  simp [rowLevel]

theorem isBottom_rows {weights : Fin n → ℕ} (hMono : Monotone weights) (t : Fin q) :
    IsBottom ((rows weights t).val) := by
  intro i j hij hi
  exact (mem_rowLevel weights t j).mpr ((mem_rowLevel weights t i).mp hi |>.trans_le (hMono hij))

theorem antitone_rows (weights : Fin n → ℕ) :
    Antitone (fun t : Fin q => (rows weights t).val) := by
  intro s t hst i hi
  exact (mem_rowLevel weights s i).mpr
    ((show s.val ≤ t.val from hst).trans_lt ((mem_rowLevel weights t i).mp hi))

/-- Of any two level sets, the one of smaller cardinality is contained in
the other. When their cardinalities agree, the sets agree. -/
theorem rows_subset_of_card_le (weights : Fin n → ℕ) (s t : Fin q)
    (h : (rows weights s).val.card ≤ (rows weights t).val.card) :
    (rows weights s).val ⊆ (rows weights t).val := by
  rcases le_total t s with hts | hst
  · exact antitone_rows weights hts
  · exact (eq_of_subset_of_card_le (antitone_rows weights hst) h).ge

theorem columnWeight_rows (weights : Fin n → ℕ) (hbound : ∀ i, weights i ≤ q) :
    columnWeight (rows (q := q) weights) = weights := by
  funext i
  change (univ.filter fun t : Fin q => i ∈ rowLevel weights t).card = weights i
  simp only [mem_rowLevel, Fin.card_filter_val_lt, min_eq_right (hbound i)]

/-- The diagonal character of a product is the product of the coordinates
raised to their occurrence counts. -/
theorem diagonalFactor_eq_prod {degree : Fin q → ℕ} (R : Selection n degree)
    (a : Fin n → ℝˣ) :
    diagonalFactor R a = ∏ i, ((a i : ℝ) : ℂ) ^ columnWeight R i := by
  unfold diagonalFactor
  simp_rw [show ∀ t : Fin q, ∏ i ∈ (R t).val, ((a i : ℝ) : ℂ) =
      ∏ i, if i ∈ (R t).val then ((a i : ℝ) : ℂ) else 1 by
    intro t
    rw [prod_ite_mem, univ_inter]]
  rw [Finset.prod_comm]
  apply prod_congr rfl
  intro i _
  rw [← prod_filter, prod_const, columnWeight]

private theorem charFun_shift (e : Fin 2) (τ : ℂ) (w : ℕ)
    (hpar : e.val = w % 2) {x : ℝ} (hx : x ≠ 0) :
    RealJacquetFrobenius.charFun e τ x =
      RealJacquetFrobenius.charFun 0 (τ - (w : ℂ)) x * (x : ℂ) ^ w := by
  have hx0 : ((|x| : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr hx)
  have hx' : (x : ℂ) = ((x / |x| : ℝ) : ℂ) * ((|x| : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, div_mul_cancel₀ _ (abs_ne_zero.mpr hx)]
  simp only [RealJacquetFrobenius.charFun, hpar, Fin.val_zero, pow_zero, one_mul]
  rw [← RealBlockPosition.sign_pow_eq_pow_mod_two hx, Complex.cpow_sub _ _ hx0,
    Complex.cpow_natCast]
  conv_rhs => rw [hx', mul_pow]
  field_simp

/-- The principal series of an even shifted list times the diagonal
character of a product gives the specified signed principal series. -/
theorem principalSeriesCharacter_shift {degree : Fin q → ℕ} (R : Selection n degree)
    (τ : Fin n → ℂ) (e : Fin n → Fin 2)
    (hpar : ∀ i, (e i).val = columnWeight R i % 2) (a : Fin n → ℝˣ) :
    principalSeriesCharacter ℝ n (realPositionCharacter (PL τ e)) a =
      principalSeriesCharacter ℝ n
        (realPositionCharacter (PL (fun i => τ i - (columnWeight R i : ℂ)) 0)) a *
        diagonalFactor R a := by
  rw [diagonalFactor_eq_prod]
  unfold principalSeriesCharacter
  rw [← prod_mul_distrib]
  apply prod_congr rfl
  intro i _
  rw [PL_position, PL_position, Pi.zero_apply, charFun_shift _ _ _ (hpar i) (a i).ne_zero]
  ring

/-- The level sets realize the prescribed parity and exponent shift. -/
theorem principalSeriesCharacter_levels (weights : Fin n → ℕ) (hbound : ∀ i, weights i ≤ q)
    (τ : Fin n → ℂ) (e : Fin n → Fin 2) (hpar : ∀ i, (e i).val = weights i % 2)
    (a : Fin n → ℝˣ) :
    principalSeriesCharacter ℝ n (realPositionCharacter (PL τ e)) a =
      principalSeriesCharacter ℝ n (realPositionCharacter (PL (fun i => τ i - (weights i : ℂ)) 0)) a *
        diagonalFactor (rows (q := q) weights) a := by
  have h := columnWeight_rows weights hbound
  have h' := principalSeriesCharacter_shift (rows (q := q) weights) τ e
    (fun i => by rw [h]; exact hpar i) a
  rwa [h] at h'

end Langlands.Archimedean.RealBottomMinorShift
