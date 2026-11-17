import Langlands.Global.RankinSelberg.WhittakerSimpleRootSchwartzBound
import Langlands.Global.RankinSelberg.SimpleRootActualGauge
import Langlands.Global.RankinSelberg.AdelicSimpleRootGaugeTorusMellin

/-! # Compact-uniform padded Whittaker integrals on the diagonal torus -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj Classical NNReal ENNReal
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

open Langlands.GeneralLinear Langlands.GroupScheme.GeneralLinear
open Unfolding GaugeDescent

local instance compactTorusSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance compactTorusSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    Smooth (Scheme F n).X.hom := GroupScheme.GeneralLinear.smoothStatement _ _

variable (F : Type u) [Field F] [NumberField F]

local instance compactTorusIdeleMeasurableSpace : MeasurableSpace (Ideles F) := borel _
local instance compactTorusIdeleBorelSpace : BorelSpace (Ideles F) := ⟨rfl⟩

/-- The padded coefficient norm on the actual diagonal idele torus, with a
determinant power and fixed real block-root weights. -/
def paddedWhittakerTorusKernel {r t : ℕ} (h : t < r)
    (W : Points F (r + 1) → ℂ) (κ : Fin (t + 1) → ℝ) (σ : ℝ)
    (c : Points F (t + 1)) (d : Fin (t + 1) → Ideles F) : ℝ≥0∞ :=
  ‖W (pad F (Nat.le_of_lt (Nat.succ_lt_succ h))
      (gaugeDiagonalPoint F (t + 1) d * c))‖ₑ *
    ENNReal.ofReal (detNorm F (t + 1) (gaugeDiagonalPoint F (t + 1) d * c) ^ σ) *
    ∏ j, ENNReal.ofReal
      (((IdeleAbsoluteValue.full F (gaugeBlockRootIdeles F t d j) : ℝ≥0) : ℝ) ^ κ j)

private theorem enorm_mul_rpow_le
    (z : ℂ) (p x y M β σ : ℝ) (hp : 0 ≤ p) (hx : 0 < x) (hy : 0 < y)
    (hM : 0 ≤ M) (hw : ‖z‖ ≤ (x * y) ^ β * p)
    (hm : y ^ (β + σ) ≤ M) :
    ‖z‖ₑ * ENNReal.ofReal ((x * y) ^ σ) ≤
      ENNReal.ofReal M * (ENNReal.ofReal (x ^ (β + σ)) * ENNReal.ofReal p) := by
  have hreal : ‖z‖ * (x * y) ^ σ ≤ M * (x ^ (β + σ) * p) := by
    calc
      _ ≤ ((x * y) ^ β * p) * (x * y) ^ σ :=
        mul_le_mul_of_nonneg_right hw (Real.rpow_nonneg (mul_pos hx hy).le _)
      _ = y ^ (β + σ) * (x ^ (β + σ) * p) := by
        rw [mul_right_comm, ← Real.rpow_add (mul_pos hx hy),
          Real.mul_rpow hx.le hy.le]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hm
        (mul_nonneg (Real.rpow_nonneg hx.le _) hp)
  have he := ENNReal.ofReal_le_ofReal hreal
  simpa only [ENNReal.ofReal_mul (norm_nonneg z), ofReal_norm,
    ENNReal.ofReal_mul hM, ENNReal.ofReal_mul (Real.rpow_nonneg hx.le _)] using he

private theorem actualGauge_padded_diagonal_formula {r t : ℕ} (hle : t + 1 ≤ r + 1)
    (Ξ : Points F (r + 1) → ℝ≥0∞) (Φ : RowVector F r → ℂ)
    (hf : ∀ (b : upperTriangularSubgroup (r + 1) (Adeles F))
      (k : PrimitiveAdelicHeight.standardCompact F (r + 1)),
      Ξ ((GeneralLinearGroupPoints.adelicEquiv F (r + 1)).symm
        ((b : AdelicGL F (r + 1)) * k)) =
          ‖Φ (gaugeSimpleRootRow F r (triangularDiagonal (r + 1) (Adeles F) b))‖ₑ)
    (d : Fin (t + 1) → Ideles F) :
    Ξ (pad F hle (gaugeDiagonalPoint F (t + 1) d)) =
      ‖Φ (gaugeSimpleRootRow F r (gaugePaddedIdeles F d))‖ₑ := by
  let b : upperTriangularSubgroup (r + 1) (Adeles F) :=
    ⟨diagonalMatrixUnits (Adeles F) (gaugePaddedIdeles F d),
      diagonalMatrixUnits_triangular _⟩
  rw [pad_gaugeDiagonalPoint]
  simpa only [b, OneMemClass.coe_one, mul_one, triangularDiagonal_diagonal,
    gaugeDiagonalPoint] using hf b 1

/-- Padded Whittaker integrals with arbitrary fixed root weights are bounded
uniformly over each compact set of right translates. The half-plane depends
only on the common determinant exponent and the fixed root weights. -/
theorem exists_padded_whittaker_compact_torus_bound
    [CompactSpace (AdeleQuotient F)] {r t : ℕ} (h : t < r)
    {V : Submodule ℂ (Points F (r + 1) → ℂ)}
    {R : ArchimedeanMatrix F (r + 1) →ₗ[ℝ] V →ₗ[ℂ] V}
    (hV : WhittakerDecayClass F r V R) (β : ℝ)
    (hβ : ∀ f : V, ∃ B : ℝ, 0 ≤ B ∧ ∀ g : Points F (r + 1),
      ‖(f : Points F (r + 1) → ℂ) g‖ ≤ B * detNorm F (r + 1) g ^ β)
    (ψ : AddChar (Adeles F) ℂ) (hψ : IsStandardAdditiveCharacter F ψ) (f : V)
    (mu : Measure (Fin (t + 1) → Ideles F)) [Measure.IsHaarMeasure mu]
    (κ : Fin (t + 1) → ℝ) (σ : ℝ) (hσ : 3 + ∑ j, |κ j| < β + σ)
    {C : Set (Points F (t + 1))} (hC : IsCompact C) :
    ∃ B : ℝ≥0∞, B < ⊤ ∧ ∀ c ∈ C,
      ∫⁻ d : Fin (t + 1) → Ideles F,
        ‖whittaker F r ψ f
          (pad F (Nat.le_of_lt (Nat.succ_lt_succ h))
            (gaugeDiagonalPoint F (t + 1) d * c))‖ₑ *
          ENNReal.ofReal
            (detNorm F (t + 1) (gaugeDiagonalPoint F (t + 1) d * c) ^ σ) *
          ∏ j, ENNReal.ofReal
            (((IdeleAbsoluteValue.full F (gaugeBlockRootIdeles F t d j) : ℝ≥0) : ℝ) ^ κ j)
        ∂mu ≤ B := by
  let hle : t + 1 ≤ r + 1 := Nat.le_of_lt (Nat.succ_lt_succ h)
  obtain ⟨a, Φ, _ha, hΦ, hbound, hsymm⟩ :=
    exists_simpleRoot_schwartzBruhat_bound F hV β hβ ψ hψ f
      (hC.image (continuous_pad F hle))
  obtain ⟨Ξ, hΞ, hformula, _hc⟩ := exists_actual_simpleRoot_gauge F a Φ hΦ hsymm
  have hdiag := actualGauge_padded_diagonal_formula F hle Ξ Φ hformula
  let H : (Fin (t + 1) → Ideles F) → ℝ≥0∞ := fun d =>
    Ξ (pad F hle (gaugeDiagonalPoint F (t + 1) d)) *
      ENNReal.ofReal (detNorm F (t + 1) (gaugeDiagonalPoint F (t + 1) d) ^ (β + σ)) *
      ∏ j, ENNReal.ofReal
        (((IdeleAbsoluteValue.full F (gaugeBlockRootIdeles F t d j) : ℝ≥0) : ℝ) ^ κ j)
  have hH : ∫⁻ d, H d ∂mu < ⊤ :=
    hΞ.lintegral_padded_torus_mul_rootWeights_of_large F h mu κ (by simpa using hσ)
  obtain ⟨M₀, hM₀⟩ := hC.bddAbove_image
    ((continuous_detNorm F (t + 1)).rpow_const
      (fun c => Or.inl (detNorm_pos F (t + 1) c).ne')).continuousOn
  let M : ℝ := max M₀ 0
  have hM0 : 0 ≤ M := le_max_right _ _
  have hM (c : Points F (t + 1)) (hc : c ∈ C) :
      detNorm F (t + 1) c ^ (β + σ) ≤ M :=
    (hM₀ (Set.mem_image_of_mem _ hc)).trans (le_max_left _ _)
  refine ⟨ENNReal.ofReal M * ∫⁻ d, H d ∂mu,
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top hH, ?_⟩
  intro c hc
  calc
    _ ≤ ∫⁻ d, ENNReal.ofReal M * H d ∂mu := by
      apply lintegral_mono
      intro d
      have hW : ‖whittaker F r ψ f
          (pad F hle (gaugeDiagonalPoint F (t + 1) d * c))‖ ≤
          detNorm F (t + 1) (gaugeDiagonalPoint F (t + 1) d * c) ^ β *
            ‖Φ (gaugeSimpleRootRow F r (gaugePaddedIdeles F d))‖ := by
        simpa only [← pad_gaugeDiagonalPoint F hle, ← pad_mul,
          UnequalAnalytic.detNorm_pad] using
          hbound (gaugePaddedIdeles F d) (pad F hle c) (Set.mem_image_of_mem _ hc)
      rw [detNorm_mul] at hW
      have he := enorm_mul_rpow_le
        (whittaker F r ψ f (pad F hle (gaugeDiagonalPoint F (t + 1) d * c)))
        ‖Φ (gaugeSimpleRootRow F r (gaugePaddedIdeles F d))‖
        (detNorm F (t + 1) (gaugeDiagonalPoint F (t + 1) d))
        (detNorm F (t + 1) c) M β σ (norm_nonneg _)
        (detNorm_pos F _ _) (detNorm_pos F _ _) hM0 hW (hM c hc)
      rw [← detNorm_mul, ofReal_norm, ← hdiag d] at he
      have he' := mul_le_mul_left he
          (∏ j, ENNReal.ofReal
            (((IdeleAbsoluteValue.full F (gaugeBlockRootIdeles F t d j) : ℝ≥0) : ℝ) ^ κ j))
      convert he' using 1
      dsimp only [H]
      ac_rfl
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

end Langlands.Global.RankinSelbergGlobal
