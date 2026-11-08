import Langlands.Representation.Conductor.SphericalAnalysis
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
# Normalized determinant and actual Iwasawa degree
-/

noncomputable section

namespace Langlands.Conductor

open MeasureTheory Langlands.GeneralLinear Langlands.Whittaker
open Langlands.HarmonicAnalysis Langlands.RankinSelberg
open Langlands.QuotientIntegration Langlands.GeneralLinear.Iwasawa

universe uF

variable {F : Type uF} [Field F] [ValuativeRel F]
variable {n : ℕ} (abv : AbsoluteValue F ℝ)

/-- The determinant norm on the actual left upper-unipotent quotient. -/
def quotientDeterminantNorm : LeftUnipotentQuotient n F → ℝ :=
  descend (upperUnipotent (n + 1) F) (fun g => abv (Matrix.det g.val)) (by
    intro u g
    simp only [Units.val_mul, Matrix.det_mul, unipotent_det, one_mul])

omit [ValuativeRel F] in
@[simp] theorem quotientDeterminantNorm_mk (g : Langlands.GeneralLinear (n + 1) F) :
    quotientDeterminantNorm abv (Quotient.mk _ g) = abv (Matrix.det g.val) := rfl

variable {ϖ : Fˣ} (hϖ : IsUniformizingElement (ValuativeRel.valuation F) ϖ)

/-- The determinant norm is the uniformizer norm to the sum of the actual
Iwasawa exponents. -/
theorem abv_det_eq_zpow_exponent
    (habv : ∀ x : F, ValuativeRel.valuation F x = 1 → abv x = 1)
    (g : Langlands.GeneralLinear (n + 1) F) :
    abv (Matrix.det g.val) = abv (ϖ : F) ^ (∑ i, exponent hϖ g i) := by
  obtain ⟨u, hu, k, hk, hg⟩ := exists_eq_exponent hϖ g
  have hdetu : Matrix.det u.val = 1 := unipotent_det ⟨u, hu⟩
  conv_lhs => rw [hg]
  rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul,
    hdetu, one_mul, map_mul, habv _ (valuation_det_of_mem_integralSubgroup hk), mul_one,
    torus_val, Matrix.det_diagonal, map_prod]
  simp only [Units.val_zpow_eq_zpow_val, map_zpow₀]
  classical
  have ha : abv (ϖ : F) ≠ 0 := (abv.pos ϖ.ne_zero).ne'
  have hprod (s : Finset (Fin (n + 1))) :
      ∏ i ∈ s, abv (ϖ : F) ^ exponent hϖ g i =
        abv (ϖ : F) ^ (∑ i ∈ s, exponent hϖ g i) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih => simp only [Finset.prod_insert hi, Finset.sum_insert hi,
        ih, zpow_add₀ ha]
  exact hprod Finset.univ

/-- With normalized uniformizer norm, quotient degree is Jacquet's
negative logarithmic determinant degree. -/
theorem quotientDeterminantNorm_eq_qpow
    (habv : ∀ x : F, ValuativeRel.valuation F x = 1 → abv x = 1)
    (q : ℕ) (hqϖ : abv (ϖ : F) = (q : ℝ)⁻¹)
    (t : LeftUnipotentQuotient n F) :
    quotientDeterminantNorm abv t = (q : ℝ) ^ (-sphericalQuotientDegree hϖ t) := by
  induction t using Quotient.inductionOn with
  | h g =>
    rw [quotientDeterminantNorm_mk, abv_det_eq_zpow_exponent abv hϖ habv g, hqϖ]
    simp only [sphericalQuotientDegree_mk, inv_zpow, zpow_neg]

/-- For `q > 1`, the determinant-norm stratum is exactly the actual degree
stratum, with the sign in Jacquet's convention. -/
theorem sphericalQuotientDegree_eq_iff_norm
    (habv : ∀ x : F, ValuativeRel.valuation F x = 1 → abv x = 1)
    (q : ℕ) (hq : 1 < q) (hqϖ : abv (ϖ : F) = (q : ℝ)⁻¹)
    (t : LeftUnipotentQuotient n F) (d : ℤ) :
    sphericalQuotientDegree hϖ t = d ↔
      quotientDeterminantNorm abv t = (q : ℝ) ^ (-d) := by
  rw [quotientDeterminantNorm_eq_qpow abv hϖ habv q hqϖ]
  have hqr : (1 : ℝ) < q := by exact_mod_cast hq
  rw [(zpow_right_strictMono₀ hqr).injective.eq_iff, neg_inj]

/-- The actual spectral weight is the `d`-th integral power of `q^(-s)`
on the degree-`d` stratum. -/
theorem determinantWeight_eq_degree_power
    (habv : ∀ x : F, ValuativeRel.valuation F x = 1 → abv x = 1)
    (q : ℕ) (hq : 0 < q) (hqϖ : abv (ϖ : F) = (q : ℝ)⁻¹)
    (g : Langlands.GeneralLinear (n + 1) F) (s : ℂ) :
    determinantWeight abv g s =
      ((q : ℂ) ^ (-s)) ^ (∑ i, exponent hϖ g i) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  rw [determinantWeight, abv_det_eq_zpow_exponent abv hϖ habv g, hqϖ,
    inv_zpow, ← zpow_neg, Complex.ofReal_zpow]
  have harg : (q : ℂ).arg = 0 := Complex.arg_ofReal_of_nonneg hq0.le
  rw [← Complex.cpow_int_mul' (by simpa [harg] using neg_lt_zero.mpr Real.pi_pos)
    (by simp [harg]; positivity) s, ← Complex.cpow_int_mul]
  congr 1
  push_cast
  ring

end Langlands.Conductor
