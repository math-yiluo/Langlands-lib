import Langlands.Global.RankinSelberg.AdelicSimpleRootGauge
import Langlands.Global.RankinSelberg.UnfoldingGL
import Mathlib.Algebra.BigOperators.Fin

/-! # Simple-root coordinates of padded adelic diagonals -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj ENNReal NNReal
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

open Unfolding

local instance gaugePaddingSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _

variable (F : Type u) [Field F] [NumberField F]

/-- Extend a tuple of diagonal ideles by identity ideles. -/
def gaugePaddedIdeles {m n : ℕ} (d : Fin m → Ideles F) : Fin n → Ideles F :=
  fun i => if hi : (i : ℕ) < m then d ⟨i, hi⟩ else 1

/-- Padding a diagonal point extends its tuple of ideles by ones. -/
theorem pad_gaugeDiagonalPoint {m n : ℕ} (h : m ≤ n) (d : Fin m → Ideles F) :
    pad F h (gaugeDiagonalPoint F m d) =
      gaugeDiagonalPoint F n (gaugePaddedIdeles F d) := by
  apply (GeneralLinearGroupPoints.adelicEquiv F n).injective
  rw [adelicEquiv_pad]
  simp only [gaugeDiagonalPoint, MulEquiv.apply_symm_apply]
  apply Units.ext
  ext i j
  rw [padGL_apply]
  simp only [GroupScheme.GeneralLinear.diagonalMatrixUnits_val, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst j
    by_cases hi : (i : ℕ) < m <;> simp [hi, gaugePaddedIdeles]
  · have hval : (i : ℕ) ≠ (j : ℕ) := fun he => hij (Fin.ext he)
    by_cases hi : (i : ℕ) < m <;> by_cases hj : (j : ℕ) < m <;>
      simp [hi, hj, hij, Fin.ext_iff, hval]

/-- The roots of a proper padded block are its internal roots, then its
last diagonal entry, and finally ones. -/
theorem gaugeSimpleRootIdeles_padded {t r : ℕ} (_h : t < r)
    (d : Fin (t + 1) → Ideles F) (i : Fin r) :
    gaugeSimpleRootIdeles F r (gaugePaddedIdeles F d) i =
      if hi : (i : ℕ) < t then gaugeSimpleRootIdeles F t d ⟨i, hi⟩
      else if (i : ℕ) = t then d (Fin.last t) else 1 := by
  by_cases hi : (i : ℕ) < t
  · have h₁ : (i : ℕ) < t + 1 := by omega
    have h₂ : (i : ℕ) + 1 < t + 1 := by omega
    simp [gaugeSimpleRootIdeles, gaugePaddedIdeles, hi, h₁, h₂]
  · by_cases ht : (i : ℕ) = t
    · simp [gaugeSimpleRootIdeles, gaugePaddedIdeles, ht]
      rfl
    · have h₁ : ¬(i : ℕ) < t + 1 := by omega
      have h₂ : ¬(i : ℕ) + 1 < t + 1 := by omega
      simp [gaugeSimpleRootIdeles, gaugePaddedIdeles, hi, ht, h₁, h₂]

/-- Adjacent ratios telescope in the idele group. -/
theorem gaugeSimpleRootIdeles_prod (r : ℕ) (d : Fin (r + 1) → Ideles F) :
    ∏ i, gaugeSimpleRootIdeles F r d i = d 0 / d (Fin.last r) := by
  simp only [gaugeSimpleRootIdeles, Finset.prod_div_distrib]
  apply div_eq_div_iff_mul_eq_mul.mpr
  exact (Fin.prod_univ_castSucc d).symm.trans (Fin.prod_univ_succ d)

/-- The product of simple-root norms is the norm of the first-to-last ratio. -/
theorem gaugeSimpleRootNormProduct_eq (r : ℕ) (d : Fin (r + 1) → Ideles F) :
    gaugeSimpleRootNormProduct F r d =
      ((IdeleAbsoluteValue.full F (d 0 / d (Fin.last r)) : ℝ≥0) : ℝ) := by
  have hp := congrArg
    (fun a : Ideles F => ((IdeleAbsoluteValue.full F a : ℝ≥0) : ℝ))
    (gaugeSimpleRootIdeles_prod F r d)
  simpa only [gaugeSimpleRootNormProduct, map_prod, Units.coe_prod, NNReal.coe_prod] using hp

/-- For a proper padded block the last diagonal entry is one, so the
product of all ambient simple-root norms is the first diagonal norm. -/
theorem gaugeSimpleRootNormProduct_padded {t r : ℕ} (h : t < r)
    (d : Fin (t + 1) → Ideles F) :
    gaugeSimpleRootNormProduct F r (gaugePaddedIdeles F d) =
      ((IdeleAbsoluteValue.full F (d 0) : ℝ≥0) : ℝ) := by
  rw [gaugeSimpleRootNormProduct_eq]
  have hr : ¬r < t + 1 := by omega
  simp [gaugePaddedIdeles, hr]

end Langlands.Global.RankinSelbergGlobal
