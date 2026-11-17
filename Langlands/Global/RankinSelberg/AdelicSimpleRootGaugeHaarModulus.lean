import Langlands.Global.RankinSelberg.AdelicSimpleRootGaugeTorusModulus
import Langlands.Global.RankinSelberg.AdelicDiagonalUnipotentModulus

/-! # Root weights for the actual diagonal conjugation modulus -/

noncomputable section
universe u
open NumberField MeasureTheory
open scoped Classical CategoryTheory.MonObj ENNReal NNReal
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

variable (F : Type u) [Field F] [NumberField F]

/-- The inverse of the actual diagonal unipotent Haar modulus, in the form
used by the compact torus quotient criterion. -/
def gaugeDiagonalInverseHaarWeight (t : ℕ)
    (d : Fin (t + 1) → Ideles F) : ℝ≥0∞ :=
  ((((AdelicDiagonalUnipotentModulus.diagonalModulus F (t + 1) d : ℝ≥0)⁻¹ :
    ℝ≥0) : ℝ≥0∞))

/-- The diagonal Haar character and the explicit positive-root norm product
have the same real value. -/
theorem diagonalModulus_toReal_eq_gaugeDiagonalModulus (t : ℕ)
    (d : Fin (t + 1) → Ideles F) :
    ((AdelicDiagonalUnipotentModulus.diagonalModulus F (t + 1) d : ℝ≥0) : ℝ) =
      gaugeDiagonalModulus F t d := by
  rw [AdelicDiagonalUnipotentModulus.diagonalModulus_eq_prod_Ioi]
  simp only [NNReal.coe_prod, gaugeDiagonalModulus, div_eq_mul_inv]

theorem gaugeDiagonalInverseHaarWeight_eq_ofReal (t : ℕ)
    (d : Fin (t + 1) → Ideles F) :
    gaugeDiagonalInverseHaarWeight F t d =
      ENNReal.ofReal (gaugeDiagonalModulus F t d)⁻¹ := by
  calc
    _ = ENNReal.ofReal
        ((((AdelicDiagonalUnipotentModulus.diagonalModulus F (t + 1) d : ℝ≥0)⁻¹ :
          ℝ≥0) : ℝ)) := ENNReal.ofReal_coe_nnreal.symm
    _ = _ := by
      rw [NNReal.coe_inv, diagonalModulus_toReal_eq_gaugeDiagonalModulus]

/-- The actual inverse Haar weight has the fixed negative root exponents. -/
theorem gaugeDiagonalInverseHaarWeight_eq_rootWeights (t : ℕ)
    (d : Fin (t + 1) → Ideles F) :
    gaugeDiagonalInverseHaarWeight F t d =
      ∏ j, ENNReal.ofReal
        (((IdeleAbsoluteValue.full F (gaugeBlockRootIdeles F t d j) : ℝ≥0) : ℝ) ^
          gaugeInverseModulusRootExponent t j) := by
  rw [gaugeDiagonalInverseHaarWeight_eq_ofReal, ofReal_gaugeDiagonalModulus_inv]

local instance haarModulusSchemeAffine (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance haarModulusSchemeSmooth (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _
local instance haarModulusIdeleMeasurableSpace : MeasurableSpace (Ideles F) := borel _
local instance haarModulusIdeleBorelSpace : BorelSpace (Ideles F) := ⟨rfl⟩

/-- The padded gauge torus estimate with the inverse of the actual diagonal
unipotent conjugation modulus. -/
theorem IsAdelicSimpleRootGauge.lintegral_padded_torus_mul_inverseHaarModulus_of_large
    [CompactSpace (AdeleQuotient F)] {r t : ℕ} (h : t < r)
    {τ : ℝ} {Ξ : Points F (r + 1) → ℝ≥0∞}
    (hΞ : IsAdelicSimpleRootGauge F r τ Ξ)
    (mu : Measure (Fin (t + 1) → Ideles F)) [Measure.IsHaarMeasure mu]
    {σ : ℝ}
    (hσ : τ + 3 + ∑ j : Fin (t + 1),
      ((((j : ℕ) + 1) * (t - (j : ℕ)) : ℕ) : ℝ) < σ) :
    ∫⁻ d : Fin (t + 1) → Ideles F,
      Ξ (pad F (Nat.le_of_lt (Nat.succ_lt_succ h))
        (gaugeDiagonalPoint F (t + 1) d)) *
        ENNReal.ofReal (detNorm F (t + 1) (gaugeDiagonalPoint F (t + 1) d) ^ σ) *
        gaugeDiagonalInverseHaarWeight F t d
      ∂mu < ⊤ := by
  simp_rw [gaugeDiagonalInverseHaarWeight_eq_ofReal]
  exact hΞ.lintegral_padded_torus_mul_inverseModulus_of_large F h mu hσ

end Langlands.Global.RankinSelbergGlobal
