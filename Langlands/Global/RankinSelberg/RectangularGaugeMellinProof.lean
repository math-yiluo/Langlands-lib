import Langlands.Global.RankinSelberg.RectangularGaugeProductBound
import Langlands.Global.RankinSelberg.AdelicSimpleRootGaugeHaarModulus
import Langlands.Global.RankinSelberg.WhittakerStandardCompactTorusIntegral
import Langlands.Global.RankinSelberg.RectangularGaugeMellinStatement

/-! # Rectangular Mellin convergence for actual adelic simple-root gauges -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj Classical ENNReal NNReal
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

open Unfolding WhittakerStandardCompactTorusIntegral

variable (F : Type u) [Field F] [NumberField F]

local instance rectangularMellinProofSchemeAffine (n : ℕ) : IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance rectangularMellinProofSchemeSmooth (n : ℕ) : Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _
private local instance : MeasurableSpace (Ideles F) := borel _
private local instance : BorelSpace (Ideles F) := ⟨rfl⟩
private local instance : LocallyCompactSpace (Ideles F) :=
  (AdelicSchwartzMellin.ideleContinuousEquiv F).symm.toHomeomorph.isClosedEmbedding.locallyCompactSpace
private local instance : SecondCountableTopology (Ideles F) :=
  (AdelicSchwartzMellin.ideleContinuousEquiv F).symm.toHomeomorph.secondCountableTopology

private theorem lintegral_torus_product_lt_top
    [CompactSpace (AdeleQuotient F)] {n : ℕ}
    (mu : Measure (Fin n → Ideles F)) [mu.IsHaarMeasure]
    {Ψ : RowVector F 1 → ℂ} (hΨ : Ψ ∈ schwartzBruhat F 1)
    (s : Fin n → ℝ) (hs : ∀ j, 3 < s j) :
    (∫⁻ a : Fin n → Ideles F,
      ∏ j, (‖Ψ (fun _ _ => (a j : Adeles F))‖ₑ *
        ENNReal.ofReal (((IdeleAbsoluteValue.full F (a j) : ℝ≥0) : ℝ) ^ s j)) ∂mu) < ⊤ := by
  have hΨc := (EqualAnalytic.schwartzBruhat_properties F 1 hΨ).1
  apply (AdelicSchwartzMellin.lintegral_continuousMulEquiv_lt_top_iff
    (ContinuousMulEquiv.refl (Fin n → Ideles F)) mu
    (Measure.pi fun _ : Fin n => (Measure.haar : Measure (Ideles F)))
      (fun a => ∏ j, (‖Ψ (fun _ _ => (a j : Adeles F))‖ₑ *
        ENNReal.ofReal (((IdeleAbsoluteValue.full F (a j) : ℝ≥0) : ℝ) ^ s j)))).mpr
  rw [AdelicSchwartzMellin.lintegral_fin_prod_eq_prod _
    (fun j => AdelicSchwartzMellin.measurable_idele_mellinKernel F hΨc (s j))]
  exact ENNReal.prod_lt_top fun j _ =>
    AdelicSchwartzMellin.lintegral_idele_schwartzBruhat_rpow_lt_top F
      (Measure.haar : Measure (Ideles F)) hΨ (hs j)

private theorem diagonal_scalarWeight (t : ℕ) (b : Fin (t + 1) → Ideles F) (s : ℝ) :
    ENNReal.ofReal (detNorm F (t + 1) (gaugeDiagonalPoint F (t + 1) b) ^ s) *
        gaugeDiagonalInverseHaarWeight F t b =
      ∏ j : Fin (t + 1), ENNReal.ofReal
        (((IdeleAbsoluteValue.full F (gaugeBlockRootIdeles F t b j) : ℝ≥0) : ℝ) ^
          (((j.val + 1 : ℕ) : ℝ) * s + gaugeInverseModulusRootExponent t j)) := by
  let A : Fin (t + 1) → ℝ := fun j =>
    ((IdeleAbsoluteValue.full F (gaugeBlockRootIdeles F t b j) : ℝ≥0) : ℝ)
  have hA : ∀ j, 0 < A j := fun j => IdeleAbsoluteValue.full_pos F _
  have hh := GaugeCoordinateRestriction.prod_rpow_weight A hA (fun j => j.val + 1) s 0
  simp only [neg_zero, Real.rpow_zero, one_mul, sub_zero] at hh
  rw [detNorm_gaugeDiagonalPoint_blockRoots, gaugeDiagonalInverseHaarWeight_eq_rootWeights]
  change ENNReal.ofReal ((∏ j, A j ^ (j.val + 1)) ^ s) * _ = _
  rw [hh, ENNReal.ofReal_prod_of_nonneg (fun j _ => Real.rpow_nonneg (hA j).le _),
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (hA j).le _), ← Real.rpow_add (hA j)]

private theorem lintegral_leading_product_inverseModulus_lt_top
    [CompactSpace (AdeleQuotient F)] (t : ℕ)
    (mu : Measure (Fin (t + 1) → Ideles F)) [mu.IsHaarMeasure]
    {Ψ : RowVector F 1 → ℂ} (hΨ : Ψ ∈ schwartzBruhat F 1) {s : ℝ}
    (hs : 3 + ∑ j : Fin (t + 1),
      ((((j : ℕ) + 1) * (t - (j : ℕ)) : ℕ) : ℝ) < s) :
    (∫⁻ b : Fin (t + 1) → Ideles F,
      (∏ j, ‖Ψ (fun _ _ => (gaugeBlockRootIdeles F t b j : Adeles F))‖ₑ) *
        ENNReal.ofReal (detNorm F (t + 1) (gaugeDiagonalPoint F (t + 1) b) ^ s) *
        gaugeDiagonalInverseHaarWeight F t b ∂mu) < ⊤ := by
  let e : Fin (t + 1) → ℝ := fun j =>
    ((j.val + 1 : ℕ) : ℝ) * s + gaugeInverseModulusRootExponent t j
  have he : ∀ j, 3 < e j := by
    intro j
    have hsum : 0 ≤ ∑ k : Fin (t + 1),
        ((((k : ℕ) + 1) * (t - (k : ℕ)) : ℕ) : ℝ) :=
      Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
    have hj : ((((j : ℕ) + 1) * (t - (j : ℕ)) : ℕ) : ℝ) ≤
        ∑ k : Fin (t + 1), ((((k : ℕ) + 1) * (t - (k : ℕ)) : ℕ) : ℝ) :=
      Finset.single_le_sum
        (f := fun k : Fin (t + 1) => ((((k : ℕ) + 1) * (t - (k : ℕ)) : ℕ) : ℝ))
        (fun _ _ => Nat.cast_nonneg _) (Finset.mem_univ j)
    have hpos : 0 ≤ s := by linarith
    have hmul : s ≤ ((j.val + 1 : ℕ) : ℝ) * s := by
      have hnat : (1 : ℝ) ≤ ((j.val + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le j.val)
      nlinarith
    dsimp [e, gaugeInverseModulusRootExponent]
    linarith
  have H := lintegral_torus_product_lt_top F mu hΨ e he
  have H' := (GaugeTorusCoordinates.lintegral_blockRoots_lt_top_iff (G := Ideles F) t mu
    (fun a => ∏ j, (‖Ψ (fun _ _ => (a j : Adeles F))‖ₑ *
      ENNReal.ofReal (((IdeleAbsoluteValue.full F (a j) : ℝ≥0) : ℝ) ^ e j)))).mpr H
  simp_rw [mul_assoc, diagonal_scalarWeight F t, ← Finset.prod_mul_distrib]
  exact H'

/-- The actual rectangular pushforward has a finite inverse-modulus torus
integral in a half-plane fixed before the individual gauge. -/
theorem IsAdelicSimpleRootGauge.lintegral_rectangular_torus_of_large
    [CompactSpace (AdeleQuotient F)] {r t : ℕ} (h : t < r) {τ : ℝ}
    {Ξ : Points F (r + 1) → ℝ≥0∞} (hΞ : IsAdelicSimpleRootGauge F r τ Ξ)
    (mu : Measure (Fin (t + 1) → Ideles F)) [mu.IsHaarMeasure] {σ : ℝ}
    (hσ : τ + 3 + ∑ j : Fin (t + 1),
      ((((j : ℕ) + 1) * (t - (j : ℕ)) : ℕ) : ℝ) < σ) :
    (∫⁻ b : Fin (t + 1) → Ideles F,
      rectangularLIntegral F h Ξ (gaugeDiagonalPoint F (t + 1) b) *
        ENNReal.ofReal (detNorm F (t + 1) (gaugeDiagonalPoint F (t + 1) b) ^ σ) *
        gaugeDiagonalInverseHaarWeight F t b ∂mu) < ⊤ := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt h)
  obtain ⟨Ψ, hΨ, M, hM, hbound⟩ := hΞ.exists_integrated_rectangular_product_bound F t d
  have H := lintegral_leading_product_inverseModulus_lt_top F t mu hΨ
    (s := σ - τ) (by linarith)
  let B : (Fin (t + 1) → Ideles F) → ℝ≥0∞ := fun b =>
    ((∏ j, ‖Ψ (fun _ _ => (gaugeBlockRootIdeles F t b j : Adeles F))‖ₑ) *
      ENNReal.ofReal (detNorm F (t + 1) (gaugeDiagonalPoint F (t + 1) b) ^ (σ - τ))) *
        gaugeDiagonalInverseHaarWeight F t b
  have hmajor : ∀ b : Fin (t + 1) → Ideles F,
      rectangularLIntegral F h Ξ (gaugeDiagonalPoint F (t + 1) b) *
        ENNReal.ofReal (detNorm F (t + 1) (gaugeDiagonalPoint F (t + 1) b) ^ σ) *
        gaugeDiagonalInverseHaarWeight F t b ≤ M * B b := by
    intro b
    rw [rectangularLIntegral_diagonal_add F t d]
    calc
      _ ≤ (M * ((∏ j, ‖Ψ (fun _ _ => (gaugeBlockRootIdeles F t b j : Adeles F))‖ₑ) *
          ENNReal.ofReal (detNorm F (t + 1) (gaugeDiagonalPoint F (t + 1) b) ^ (σ - τ)))) *
            gaugeDiagonalInverseHaarWeight F t b := mul_le_mul' (hbound b σ) le_rfl
      _ = M * B b := mul_assoc _ _ _
  refine (lintegral_mono hmajor).trans_lt ?_
  rw [lintegral_const_mul' _ _ hM.ne]
  exact ENNReal.mul_lt_top hM H

/-- The weighted rectangular pushforward is integrable on the actual
Whittaker quotient at the same common threshold. -/
theorem IsAdelicSimpleRootGauge.lintegral_rectangular_whittakerQuotient_of_large
    [CompactSpace (AdeleQuotient F)] {r t : ℕ} (h : t < r) {τ : ℝ}
    {Ξ : Points F (r + 1) → ℝ≥0∞} (hΞ : IsAdelicSimpleRootGauge F r τ Ξ) {σ : ℝ}
    (hσ : τ + 3 + ∑ j : Fin (t + 1),
      ((((j : ℕ) + 1) * (t - (j : ℕ)) : ℕ) : ℝ) < σ) :
    (∫⁻ p : WhittakerQuotient F (t + 1),
      rectangularLIntegral F h Ξ p.out * ENNReal.ofReal (detNorm F (t + 1) p.out ^ σ)
        ∂whittakerQuotientMeasure F (t + 1)) < ⊤ := by
  let f : Points F (t + 1) → ℝ≥0∞ := fun g =>
    rectangularLIntegral F h Ξ g * ENNReal.ofReal (detNorm F (t + 1) g ^ σ)
  have hpow : Continuous fun g : Points F (t + 1) => detNorm F (t + 1) g ^ σ :=
    (continuous_detNorm F (t + 1)).rpow_const fun g => Or.inl (detNorm_pos F _ g).ne'
  have hfm : Measurable f := (measurable_rectangularLIntegral F h hΞ.2.1).mul
    (ENNReal.measurable_ofReal.comp hpow.measurable)
  have hfN : ∀ (v : unipotentAdelic F (t + 1)) (g : Points F (t + 1)),
      f ((v : Points F (t + 1)) * g) = f g := by
    intro v g
    dsimp only [f]
    rw [rectangularLIntegral_unipotent_mul F h Ξ hΞ.2.2.1,
      detNorm_mul, detNorm_unipotent, one_mul]
  have hfK : IsRightStandardCompactInvariant F (t + 1) f := by
    intro k g
    dsimp only [f]
    rw [rectangularLIntegral_standardCompact_mul_of_simpleRootGauge F h hΞ,
      detNorm_mul, detNorm_eq_one_of_mem_standardCompact F k.property, mul_one]
  apply lintegral_whittakerQuotient_lt_top_of_single F (t + 1)
    (Measure.haar : Measure (Fin (t + 1) → Ideles F)) f hfm hfN hfK
  simpa only [f, gaugeDiagonalInverseHaarWeight, mul_comm] using
    hΞ.lintegral_rectangular_torus_of_large F h
      (Measure.haar : Measure (Fin (t + 1) → Ideles F)) hσ

/-- The unchanged published rectangular Mellin proposition. -/
theorem adelicSimpleRootGaugeRectangularMellin :
    AdelicSimpleRootGaugeRectangularMellinStatement.{u} := by
  intro F _ _ _ r t h τ _hτ
  let T := τ + 3 + ∑ j : Fin (t + 1),
    ((((j : ℕ) + 1) * (t - (j : ℕ)) : ℕ) : ℝ)
  refine ⟨max 0 T, le_max_left _ _, fun Ξ hΞ σ hσ => ?_⟩
  exact hΞ.lintegral_rectangular_whittakerQuotient_of_large F h
    ((le_max_right 0 T).trans_lt hσ)

end Langlands.Global.RankinSelbergGlobal
