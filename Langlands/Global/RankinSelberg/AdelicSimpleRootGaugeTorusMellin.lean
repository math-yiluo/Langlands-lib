import Langlands.Global.RankinSelberg.AdelicSchwartzMellinProduct
import Langlands.Global.RankinSelberg.AdelicSimpleRootGaugeSchwartzRestriction

/-! # Padded simple-root gauge convergence on the diagonal torus -/

noncomputable section
universe u
open NumberField MeasureTheory
open scoped Classical CategoryTheory.MonObj ENNReal NNReal
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

variable (F : Type u) [Field F] [NumberField F]

local instance torusMellinSchemeAffine (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance torusMellinSchemeSmooth (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _
local instance torusMellinIdeleMeasurableSpace : MeasurableSpace (Ideles F) := borel _
local instance torusMellinIdeleBorelSpace : BorelSpace (Ideles F) := ⟨rfl⟩
local instance torusMellinIdeleLocallyCompact : LocallyCompactSpace (Ideles F) :=
  (AdelicSchwartzMellin.ideleContinuousEquiv F).symm.toHomeomorph.isClosedEmbedding.locallyCompactSpace
local instance torusMellinIdeleSecondCountable : SecondCountableTopology (Ideles F) :=
  (AdelicSchwartzMellin.ideleContinuousEquiv F).symm.toHomeomorph.secondCountableTopology

/-- Padded diagonal convergence, allowing any fixed additional powers of the
block roots. Each resulting root exponent must be greater than three. -/
theorem IsAdelicSimpleRootGauge.lintegral_padded_torus_mul_rootWeights_lt_top
    [CompactSpace (AdeleQuotient F)] {r t : ℕ} (h : t < r)
    {τ : ℝ} {Ξ : Points F (r + 1) → ℝ≥0∞}
    (hΞ : IsAdelicSimpleRootGauge F r τ Ξ)
    (mu : Measure (Fin (t + 1) → Ideles F)) [Measure.IsHaarMeasure mu]
    (σ : ℝ) (κ : Fin (t + 1) → ℝ)
    (hσ : ∀ j : Fin (t + 1), 3 < (((j : ℕ) + 1 : ℕ) : ℝ) * σ - τ + κ j) :
    ∫⁻ d : Fin (t + 1) → Ideles F,
      Ξ (pad F (Nat.le_of_lt (Nat.succ_lt_succ h))
        (gaugeDiagonalPoint F (t + 1) d)) *
        ENNReal.ofReal (detNorm F (t + 1) (gaugeDiagonalPoint F (t + 1) d) ^ σ) *
        ∏ j, ENNReal.ofReal
          (((IdeleAbsoluteValue.full F (gaugeBlockRootIdeles F t d j) : ℝ≥0) : ℝ) ^ κ j)
      ∂mu < ⊤ := by
  obtain ⟨Φ, hΦ, hdiag⟩ := hΞ.2.2.2.2
  let Ψ : RowVector F (t + 1) → ℂ := Φ ∘ gaugeExtendRootRow F
  have hΨ : Ψ ∈ schwartzBruhat F (t + 1) :=
    schwartzBruhat_comp_gaugeExtendRootRow F h hΦ
  let f : (Fin (t + 1) → Ideles F) → ℝ≥0∞ := fun a =>
    ‖Ψ (fun _ j => (a j : Adeles F))‖ₑ *
      ∏ j, ENNReal.ofReal
        (((IdeleAbsoluteValue.full F (a j) : ℝ≥0) : ℝ) ^
          ((((j : ℕ) + 1 : ℕ) : ℝ) * σ - τ + κ j))
  have hint : ∫⁻ a, f a ∂mu < ⊤ :=
    AdelicSchwartzMellin.lintegral_idele_torus_schwartzBruhat_rpow_lt_top F
      (Nat.succ_pos t) mu hΨ _ hσ
  have hroot := (GaugeTorusCoordinates.lintegral_blockRoots_lt_top_iff t mu f).mpr hint
  convert hroot using 1
  apply lintegral_congr
  intro d
  change _ = ‖Φ (gaugeExtendRootRow F (gaugeBlockRootRow F t d))‖ₑ *
    ∏ j, ENNReal.ofReal
      (((IdeleAbsoluteValue.full F (gaugeBlockRootIdeles F t d j) : ℝ≥0) : ℝ) ^
        ((((j : ℕ) + 1 : ℕ) : ℝ) * σ - τ + κ j))
  rw [pad_gaugeDiagonalPoint, hdiag, gaugeSimpleRootRow_padded F h]
  calc
    _ = ‖Φ (gaugeExtendRootRow F (gaugeBlockRootRow F t d))‖ₑ *
        ((ENNReal.ofReal
          (gaugeSimpleRootNormProduct F r (gaugePaddedIdeles F d) ^ (-τ)) *
          ENNReal.ofReal (detNorm F (t + 1) (gaugeDiagonalPoint F (t + 1) d) ^ σ)) *
          ∏ j, ENNReal.ofReal
            (((IdeleAbsoluteValue.full F (gaugeBlockRootIdeles F t d j) : ℝ≥0) : ℝ) ^
              κ j)) := by ac_rfl
    _ = _ := by
      rw [gaugePadded_scalarWeight F h, ← Finset.prod_mul_distrib]
      congr 1
      apply Finset.prod_congr rfl
      intro j _
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (IdeleAbsoluteValue.full_pos F _).le _),
        ← Real.rpow_add (IdeleAbsoluteValue.full_pos F _)]

/-- A uniform half-plane for the weighted padded torus integral. The threshold
depends on the gauge exponent and the fixed root weights, not on the gauge. -/
theorem IsAdelicSimpleRootGauge.lintegral_padded_torus_mul_rootWeights_of_large
    [CompactSpace (AdeleQuotient F)] {r t : ℕ} (h : t < r)
    {τ : ℝ} {Ξ : Points F (r + 1) → ℝ≥0∞}
    (hΞ : IsAdelicSimpleRootGauge F r τ Ξ)
    (mu : Measure (Fin (t + 1) → Ideles F)) [Measure.IsHaarMeasure mu]
    (κ : Fin (t + 1) → ℝ) {σ : ℝ}
    (hσ : τ + 3 + ∑ j, |κ j| < σ) :
    ∫⁻ d : Fin (t + 1) → Ideles F,
      Ξ (pad F (Nat.le_of_lt (Nat.succ_lt_succ h))
        (gaugeDiagonalPoint F (t + 1) d)) *
        ENNReal.ofReal (detNorm F (t + 1) (gaugeDiagonalPoint F (t + 1) d) ^ σ) *
        ∏ j, ENNReal.ofReal
          (((IdeleAbsoluteValue.full F (gaugeBlockRootIdeles F t d j) : ℝ≥0) : ℝ) ^ κ j)
      ∂mu < ⊤ := by
  apply hΞ.lintegral_padded_torus_mul_rootWeights_lt_top F h mu σ κ
  intro j
  have hsum : 0 ≤ ∑ j, |κ j| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hσpos : 0 ≤ σ := by linarith [hΞ.1]
  have hj : (1 : ℝ) ≤ (((j : ℕ) + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le (j : ℕ))
  have hweight := mul_le_mul_of_nonneg_right hj hσpos
  have habs : |κ j| ≤ ∑ i, |κ i| :=
    Finset.single_le_sum (f := fun i : Fin (t + 1) => |κ i|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
  linarith [neg_abs_le (κ j)]

/-- Without extra root weights, the half-plane `σ > τ + 3` suffices for every
proper padded diagonal torus and every Haar normalization. -/
theorem IsAdelicSimpleRootGauge.lintegral_padded_torus_of_large
    [CompactSpace (AdeleQuotient F)] {r t : ℕ} (h : t < r)
    {τ : ℝ} {Ξ : Points F (r + 1) → ℝ≥0∞}
    (hΞ : IsAdelicSimpleRootGauge F r τ Ξ)
    (mu : Measure (Fin (t + 1) → Ideles F)) [Measure.IsHaarMeasure mu]
    {σ : ℝ} (hσ : τ + 3 < σ) :
    ∫⁻ d : Fin (t + 1) → Ideles F,
      Ξ (pad F (Nat.le_of_lt (Nat.succ_lt_succ h))
        (gaugeDiagonalPoint F (t + 1) d)) *
        ENNReal.ofReal (detNorm F (t + 1) (gaugeDiagonalPoint F (t + 1) d) ^ σ)
      ∂mu < ⊤ := by
  simpa only [Real.rpow_zero, ENNReal.ofReal_one, Finset.prod_const_one, mul_one,
    abs_zero, Finset.sum_const_zero, add_zero] using
    hΞ.lintegral_padded_torus_mul_rootWeights_of_large F h mu (fun _ => 0)
      (by simpa only [abs_zero, Finset.sum_const_zero, add_zero] using hσ)

end Langlands.Global.RankinSelbergGlobal
