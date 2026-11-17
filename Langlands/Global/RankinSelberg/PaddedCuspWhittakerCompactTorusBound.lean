import Langlands.Global.RankinSelberg.PaddedWhittakerCompactTorusBound
import Langlands.Global.RankinSelberg.AdelicSimpleRootGaugeHaarModulus
import Langlands.Global.RankinSelberg.UnequalGaugeReduction
import Langlands.Global.RankinSelberg.WhittakerExpansionCore.ExpansionRealization

/-! # Compact torus bounds for actual padded cuspidal Whittaker functions -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj Classical NNReal ENNReal
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

open Unfolding

local instance paddedCuspSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance paddedCuspSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    Smooth (Scheme F n).X.hom := GroupScheme.GeneralLinear.smoothStatement _ _

variable (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]

local instance paddedCuspIdeleMeasurableSpace : MeasurableSpace (Ideles F) := borel _
local instance paddedCuspIdeleBorelSpace : BorelSpace (Ideles F) := ⟨rfl⟩

/-- The actual nonnegative padded cuspidal Whittaker integrand. -/
def paddedCuspWhittakerNormWeight {r t : ℕ} (h : t < r)
    (T : Automorphic.CuspidalOperatorRealization F r)
    (ψ : AddChar (Adeles F) ℂ) (v : T.Space) (σ : ℝ)
    (g : Points F (t + 1)) : ℝ≥0∞ :=
  ‖cuspWhittaker F T ψ v
    (pad F (Nat.le_of_lt (Nat.succ_lt_succ h)) g)‖ₑ *
      ENNReal.ofReal (detNorm F (t + 1) g ^ σ)

theorem measurable_paddedCuspWhittakerNormWeight {r t : ℕ} (h : t < r)
    (T : Automorphic.CuspidalOperatorRealization F r)
    (ψ : AddChar (Adeles F) ℂ) (hψ : IsStandardAdditiveCharacter F ψ)
    (v : T.Space) (σ : ℝ) :
    Measurable (paddedCuspWhittakerNormWeight F h T ψ v σ) :=
  ((measurable_cuspWhittaker F T ψ hψ v).comp
    (continuous_pad F _).measurable).enorm.mul
      ((continuous_detNorm F (t + 1)).measurable.pow_const σ).ennreal_ofReal

theorem paddedCuspWhittakerNormWeight_unipotent_mul {r t : ℕ} (h : t < r)
    (T : Automorphic.CuspidalOperatorRealization F r)
    (ψ : AddChar (Adeles F) ℂ) (hψ : IsStandardAdditiveCharacter F ψ)
    (v : T.Space) (σ : ℝ) (x : unipotentAdelic F (t + 1))
    (g : Points F (t + 1)) :
    paddedCuspWhittakerNormWeight F h T ψ v σ ((x : Points F (t + 1)) * g) =
      paddedCuspWhittakerNormWeight F h T ψ v σ g := by
  simp only [paddedCuspWhittakerNormWeight]
  rw [← ofReal_norm, ← ofReal_norm,
    GaugeReduction.norm_cuspWhittaker_pad_unipotent_mul F h T ψ hψ v x g,
    GaugeReduction.detNorm_unipotent_mul]

theorem sum_abs_gaugeInverseModulusRootExponent (t : ℕ) :
    ∑ j : Fin (t + 1), |gaugeInverseModulusRootExponent t j| =
      ∑ j : Fin (t + 1), ((((j : ℕ) + 1) * (t - (j : ℕ)) : ℕ) : ℝ) := by
  apply Finset.sum_congr rfl
  intro j _
  rw [gaugeInverseModulusRootExponent, abs_neg,
    abs_of_nonneg (show (0 : ℝ) ≤
      ((((j : ℕ) + 1) * (t - (j : ℕ)) : ℕ) : ℝ) from Nat.cast_nonneg _)]

/-- A common determinant bound for a cuspidal realization gives the
compact-uniform torus bound with the actual inverse diagonal Haar modulus. -/
theorem exists_padded_cusp_whittaker_compact_torus_bound {r t : ℕ} (h : t < r)
    (T : Automorphic.CuspidalOperatorRealization F r) (β : ℝ)
    (hβ : ∀ v : T.Space, ∃ B : ℝ, 0 ≤ B ∧ ∀ g : Points F (r + 1),
      ‖cuspFunction F T v g‖ ≤ B * detNorm F (r + 1) g ^ β)
    (ψ : AddChar (Adeles F) ℂ) (hψ : IsStandardAdditiveCharacter F ψ)
    (v : T.Space)
    (mu : Measure (Fin (t + 1) → Ideles F)) [Measure.IsHaarMeasure mu]
    (σ : ℝ)
    (hσ : 3 + ∑ j : Fin (t + 1),
      ((((j : ℕ) + 1) * (t - (j : ℕ)) : ℕ) : ℝ) < β + σ)
    {C : Set (Points F (t + 1))} (hC : IsCompact C) :
    ∃ B : ℝ≥0∞, B < ⊤ ∧ ∀ c ∈ C,
      ∫⁻ d : Fin (t + 1) → Ideles F,
        gaugeDiagonalInverseHaarWeight F t d *
          paddedCuspWhittakerNormWeight F h T ψ v σ
            (gaugeDiagonalPoint F (t + 1) d * c)
        ∂mu ≤ B := by
  have hβV : ∀ f : cuspSpace F T, ∃ B : ℝ, 0 ≤ B ∧ ∀ g : Points F (r + 1),
      ‖(f : Points F (r + 1) → ℂ) g‖ ≤ B * detNorm F (r + 1) g ^ β := by
    intro f
    rw [coe_eq_cuspFunction]
    exact hβ _
  obtain ⟨B, hB, hbound⟩ := exists_padded_whittaker_compact_torus_bound F h
    (whittakerDecayClass_cuspSpace F T) β hβV ψ hψ (cuspEquiv F T v)
    mu (gaugeInverseModulusRootExponent t) σ
    (by simpa only [sum_abs_gaugeInverseModulusRootExponent] using hσ) hC
  refine ⟨B, hB, fun c hc => ?_⟩
  convert hbound c hc using 1
  apply lintegral_congr
  intro d
  rw [gaugeDiagonalInverseHaarWeight_eq_rootWeights]
  change _ * (‖cuspWhittaker F T ψ v _‖ₑ * _) = _
  ac_rfl

end Langlands.Global.RankinSelbergGlobal
