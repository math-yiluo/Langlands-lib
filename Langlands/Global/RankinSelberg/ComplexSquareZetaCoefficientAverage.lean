import Langlands.Analysis.SchwartzCompactAverage
import Langlands.Global.RankinSelberg.ComplexLocalWhittakerChangeCharacter
import Langlands.Global.RankinSelberg.ComplexSquareZetaConvergence

/-! # Moving compact coefficient averages to the square Schwartz test -/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Operator SchwartzMap

namespace Langlands.Global.RankinSelbergGlobal.ComplexSquareZeta

open Langlands.Archimedean Langlands.GeneralLinear
open ComplexGodement (normPower)
open ComplexCharacterChange (complexMatrixHeight_mul_le)
open ComplexMaximalParabolicIntegration (normSqC normSqC_det_unitary)

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

local instance squareCoefficientGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear n ℂ) := borel _
local instance squareCoefficientGLBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear n ℂ) := ⟨rfl⟩
local instance squareCoefficientGLSecondCountable (n : ℕ) :
    SecondCountableTopology (Langlands.GeneralLinear n ℂ) :=
  Units.isOpenEmbedding_val.isEmbedding.secondCountableTopology

variable {r : ℕ}
local notation "Rank" => r.succ
local notation "G" => Langlands.GeneralLinear r.succ ℂ
local notation "K" => unitaryCompact ℂ r.succ
local notation "Mat" => Matrix (Fin r.succ) (Fin r.succ) ℂ

/-- A compact weighted coefficient of left translates of a function on the group. -/
def compactCoefficient (κ : Measure K) (u : K → K) (w : K → ℂ) (f : G → ℂ) (g : G) : ℂ :=
  ∫ k, w k * f ((u k).val * g) ∂κ

private def leftInverseAction (k : K) : Mat →L[ℝ] Mat :=
  ContinuousLinearMap.mul ℝ Mat k.val⁻¹.val

private def unitaryBound (r : ℕ) : ℝ :=
  max 1 (sSup (Set.range fun k : unitaryCompact ℂ r.succ => ‖k.val.val‖))

private theorem norm_le_leftInverseAction (M : Mat) (k : K) :
    ‖M‖ ≤ unitaryBound r * ‖leftInverseAction k M‖ := by
  have hcont : Continuous (fun k : K => k.val.val) :=
    Units.continuous_val.comp continuous_subtype_val
  have hb := (isCompact_range hcont.norm).bddAbove
  have hK : ‖k.val.val‖ ≤ unitaryBound r :=
    (le_csSup hb (Set.mem_range_self k)).trans (le_max_right _ _)
  change ‖M‖ ≤ unitaryBound r * ‖k.val⁻¹.val * M‖
  calc
    ‖M‖ = ‖k.val.val * (k.val⁻¹.val * M)‖ := by
      rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
    _ ≤ ‖k.val.val‖ * ‖k.val⁻¹.val * M‖ := norm_mul_le _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right hK (norm_nonneg _)

/-- The weighted compact average of a square Schwartz test translated by inverse unitary
matrices on the left. -/
def leftAverageInv (κ : Measure K) [IsFiniteMeasure κ] (u : K → K) (hu : Continuous u)
    (w : K → ℂ) (hw : Continuous w) (Φ : 𝓢(Mat, ℂ)) : 𝓢(Mat, ℂ) :=
  Langlands.Analysis.SchwartzCompactAverage.average w (leftInverseAction ∘ u) Φ κ hw
    (((ContinuousLinearMap.mul ℝ Mat).continuous.comp
      (Units.continuous_val.comp continuous_subtype_val.inv)).comp hu)
    (zero_le_one.trans (le_max_left _ _))
    (fun M k => norm_le_leftInverseAction M (u k))

theorem leftAverageInv_apply (κ : Measure K) [IsFiniteMeasure κ] (u : K → K) (hu : Continuous u)
    (w : K → ℂ) (hw : Continuous w) (Φ : 𝓢(Mat, ℂ)) (M : Mat) :
    leftAverageInv κ u hu w hw Φ M = ∫ k, w k * Φ ((u k).val⁻¹.val * M) ∂κ := rfl

private theorem continuous_complexMatrixHeight : Continuous (complexMatrixHeight (n := Rank)) := by
  unfold complexMatrixHeight
  have h : Continuous (fun g : G => g.val) := Units.continuous_val
  have hi : Continuous (fun g : G => g⁻¹.val) := Units.continuous_coe_inv
  exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    ((h.matrix_elem i j).norm.pow 2).add ((hi.matrix_elem i j).norm.pow 2)

private theorem complexMatrixHeight_nonneg (g : G) : 0 ≤ complexMatrixHeight g := by
  unfold complexMatrixHeight
  positivity

private theorem integrable_coefficient_kernel (μ : Measure G) [μ.IsHaarMeasure]
    (κ : Measure K) [IsFiniteMeasure κ] (u : K → K) (hu : Continuous u)
    (w : K → ℂ) (hw : Continuous w) (Φ : 𝓢(Mat, ℂ)) {f : G → ℂ} (hf : Continuous f)
    {M : ℕ} {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ g, ‖f g‖ ≤ C * complexMatrixHeight g ^ M)
    (p : ℂ) (hp : (Rank : ℝ) + M ≤ p.re) :
    Integrable (fun x : K × G => w x.1 * Φ x.2.val * f ((u x.1).val * x.2) *
      normPower p (determinant x.2)) (κ.prod μ) := by
  let B (g : G) := (complexMatrixHeight g ^ M : ℝ) * Φ g.val * normPower p (determinant g)
  have hB : Integrable B μ := integrable_height_detNormPower μ M Φ p hp
  have hu' : Continuous (fun k : K => (u k).val) := continuous_subtype_val.comp hu
  have hh := continuous_complexMatrixHeight.comp hu'
  obtain ⟨D₀, hD₀⟩ := (isCompact_range hh).bddAbove
  obtain ⟨W₀, hW₀⟩ := (isCompact_range hw.norm).bddAbove
  let D := max D₀ 0
  let W := max W₀ 0
  have hD (k : K) : complexMatrixHeight (u k).val ≤ D :=
    (hD₀ (Set.mem_range_self k)).trans (le_max_left _ _)
  have hW (k : K) : ‖w k‖ ≤ W := (hW₀ (Set.mem_range_self k)).trans (le_max_left _ _)
  have hI := (hB.norm.comp_snd κ).const_mul (W * C * D ^ M)
  refine hI.mono' ?_ (ae_of_all _ fun x => ?_)
  · exact ((((hw.comp continuous_fst).mul (Φ.continuous.comp
      (Units.continuous_val.comp continuous_snd))).mul
      (hf.comp ((hu'.comp continuous_fst).mul continuous_snd))).mul
      ((continuous_detNormPower p).comp continuous_snd)).aestronglyMeasurable
  have hKg : ‖f ((u x.1).val * x.2)‖ ≤ C * (D * complexMatrixHeight x.2) ^ M := by
    apply (hbound _).trans
    apply mul_le_mul_of_nonneg_left _ hC
    apply pow_le_pow_left₀ (complexMatrixHeight_nonneg _)
    exact (complexMatrixHeight_mul_le _ _).trans
      (mul_le_mul_of_nonneg_right (hD _) (complexMatrixHeight_nonneg _))
  simp only [B, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (complexMatrixHeight_nonneg x.2) _)]
  calc
    _ ≤ W * ‖Φ x.2.val‖ * (C * (D * complexMatrixHeight x.2) ^ M) *
        ‖normPower p (determinant x.2)‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact mul_le_mul (mul_le_mul_of_nonneg_right (hW _) (norm_nonneg _)) hKg
        (norm_nonneg _) (mul_nonneg (le_max_right _ _) (norm_nonneg _))
    _ = _ := by rw [mul_pow]; ring

private theorem detNormPower_unitary (p : ℂ) (k : K) :
    normPower p (determinant k.val) = 1 := by
  change normSqC k.val.val.det ^ p = 1
  rw [normSqC_det_unitary k, Complex.one_cpow]

/-- Moving a compact average of the coefficient through the square zeta integral gives the
left average of the Schwartz test. The common height bound ensures absolute integrability. -/
def ComplexSquareZetaCoefficientAverageStatement : Prop :=
  ∀ (μ : Measure G) [μ.IsHaarMeasure] (κ : Measure K) [IsFiniteMeasure κ]
    (u : K → K) (hu : Continuous u) (w : K → ℂ) (hw : Continuous w)
    (Φ : 𝓢(Mat, ℂ)) (f : G → ℂ), Continuous f → ∀ (M : ℕ) (C : ℝ), 0 ≤ C →
    (∀ g, ‖f g‖ ≤ C * complexMatrixHeight g ^ M) → ∀ (s : ℂ),
    (Rank : ℝ) + M ≤ (s + ((Rank : ℂ) - 1) / 2).re →
    Integrable (zetaKernel Φ (compactCoefficient κ u w f) s) μ ∧
    (∫ g, zetaKernel Φ (compactCoefficient κ u w f) s g ∂μ) =
      ∫ g, zetaKernel (leftAverageInv κ u hu w hw Φ) f s g ∂μ

theorem complexSquareZetaCoefficientAverage : ComplexSquareZetaCoefficientAverageStatement (r := r) := by
  intro μ _ κ _ u hu w hw Φ f hf M C hC hbound s hs
  let p := s + ((Rank : ℂ) - 1) / 2
  let I (k : K) (g : G) := w k * Φ g.val * f ((u k).val * g) * normPower p (determinant g)
  let J (k : K) (g : G) := I k ((u k).val⁻¹ * g)
  have hi : Integrable (Function.uncurry I) (κ.prod μ) :=
    integrable_coefficient_kernel μ κ u hu w hw Φ hf hC hbound p hs
  have hjEq (k : K) (g : G) : J k g =
      w k * Φ ((u k).val⁻¹.val * g.val) * f g * normPower p (determinant g) := by
    change I k ((u k).val⁻¹ * g) = _
    have hk : (u k).val * ((u k).val⁻¹ * g) = g := by
      rw [← mul_assoc, mul_inv_cancel, one_mul]
    unfold I
    rw [hk]
    simp only [Units.val_mul, map_mul, one_mul,
      ← show ((u k)⁻¹ : K).val = (u k).val⁻¹ from rfl, detNormPower_unitary]
  have hjCont : Continuous (Function.uncurry J) := by
    have hK := (continuous_subtype_val.comp hu).inv.comp (continuous_fst : Continuous (Prod.fst : K × G → K))
    have hM := (Units.continuous_val.comp hK).matrix_mul (Units.continuous_val.comp continuous_snd)
    simp_rw [Function.uncurry_def, hjEq]
    exact (((hw.comp continuous_fst).mul (Φ.continuous.comp hM)).mul
      (hf.comp continuous_snd)).mul ((continuous_detNormPower p).comp continuous_snd)
  have hj : Integrable (Function.uncurry J) (κ.prod μ) := by
    refine (integrable_prod_iff hjCont.aestronglyMeasurable).2 ⟨?_, ?_⟩
    · filter_upwards [hi.prod_right_ae] with k hk
      exact (measurePreserving_mul_left μ (u k).val⁻¹).integrable_comp_of_integrable hk
    have hnorm (k : K) : (∫ g, ‖J k g‖ ∂μ) = ∫ g, ‖I k g‖ ∂μ :=
      integral_mul_left_eq_self (fun g => ‖I k g‖) _
    simpa only [Function.uncurry_apply_pair, hnorm] using
      (integrable_prod_iff hi.aestronglyMeasurable).1 hi |>.2
  have hIavg (g : G) : zetaKernel Φ (compactCoefficient κ u w f) s g = ∫ k, I k g ∂κ := by
    change Φ g.val * (∫ k, w k * f ((u k).val * g) ∂κ) * normPower p (determinant g) = _
    rw [← integral_const_mul, ← integral_mul_const]
    apply integral_congr_ae
    filter_upwards with k
    dsimp [I]
    ring
  have hJavg (g : G) : zetaKernel (leftAverageInv κ u hu w hw Φ) f s g = ∫ k, J k g ∂κ := by
    rw [zetaKernel, leftAverageInv_apply, ← integral_mul_const, ← integral_mul_const]
    apply integral_congr_ae
    filter_upwards with k
    exact (hjEq k g).symm
  refine ⟨hi.integral_prod_right.congr (ae_of_all _ fun g => (hIavg g).symm), ?_⟩
  simp_rw [hIavg, hJavg]
  rw [← integral_integral_swap hi, ← integral_integral_swap hj]
  apply integral_congr_ae
  filter_upwards with k
  exact (integral_mul_left_eq_self (fun g => I k g) (u k).val⁻¹).symm

end Langlands.Global.RankinSelbergGlobal.ComplexSquareZeta
