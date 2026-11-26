import Langlands.Global.RankinSelberg.RealGodementRowFourierInversion
import Langlands.Global.RankinSelberg.RealLocalWhittakerModel
import Langlands.Representation.Archimedean.SmoothCompactOrbitIntegral
import Langlands.Representation.Archimedean.SmoothModerateGrowth
import Langlands.Representation.Archimedean.SmoothAction
import Langlands.Representation.RankinSelberg.ZeroRowLastRowCutoffProof

/-! # Schwartz row multiplication on real smooth Whittaker coefficients -/

noncomputable section

open MeasureTheory Matrix
open scoped ContDiff Manifold Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 650000

namespace Langlands.Global.RankinSelbergGlobal.RealSmoothRowAbsorption

open Langlands.Archimedean Langlands.HarmonicAnalysis Langlands.LocalFactor.Archimedean
open Langlands.RankinSelberg (appendIdentity appendIdentity_mul_zeroRowColumnUnipotent lastRow
  zeroRowColumnEntries zeroRowColumnUnipotent zeroRowColumnUnipotent_mem_upperUnipotent
  zeroRowColumnUnipotent_superdiagonal_sum continuous_zeroRowColumnUnipotent)
open ArchimedeanLocal DerivativeSmoothVectors

universe u

variable {r d : ℕ} {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

local notation "n" => r + (d + 1) + 1
local notation "G" => Langlands.GeneralLinear n ℝ
local notation "X" => (Fin (r + 1) → ℝ)
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation "I" => matrixModel ℝ n
local notation:max "D" R:max => DerivativeSmoothVectors I R
local notation "j" => zeroRowColumnUnipotent (F := ℝ) r d

private def columnCLM : X →L[ℝ] Mat :=
  ({ toFun := zeroRowColumnEntries r d
     map_add' x y := by
       ext i k
       by_cases hi : i.val < r + 1 <;> by_cases hk : k.val = r + 1 <;>
         simp only [zeroRowColumnEntries, hi, hk, ↓reduceDIte, ↓reduceIte, Matrix.add_apply,
           Pi.add_apply, add_zero]
     map_smul' c x := by
       ext i k
       by_cases hi : i.val < r + 1 <;> by_cases hk : k.val = r + 1 <;>
         simp only [zeroRowColumnEntries, hi, hk, ↓reduceDIte, ↓reduceIte, Matrix.smul_apply,
           Pi.smul_apply, RingHom.id_apply, smul_zero] } : X →ₗ[ℝ] Mat).toContinuousLinearMap

private theorem unitHeight_column_le (x : X) :
    unitHeight (j x) ≤ (1 + ‖(1 : Mat)‖ + ‖columnCLM (r := r) (d := d)‖) * max 1 ‖x‖ := by
  let c := columnCLM (r := r) (d := d)
  let C : ℝ := 1 + ‖(1 : Mat)‖ + ‖c‖
  have hC : 1 ≤ C := by
    dsimp [C]
    linarith only [norm_nonneg (1 : Mat), norm_nonneg c]
  have hx : 1 ≤ max 1 ‖x‖ := le_max_left _ _
  have hc := c.le_opNorm x
  change ‖zeroRowColumnEntries r d x‖ ≤ ‖c‖ * ‖x‖ at hc
  have hbound : ‖(1 : Mat)‖ + ‖zeroRowColumnEntries r d x‖ ≤ C * max 1 ‖x‖ := by
    calc
      _ ≤ ‖(1 : Mat)‖ * max 1 ‖x‖ + ‖c‖ * max 1 ‖x‖ :=
        add_le_add (le_mul_of_one_le_right (norm_nonneg _) hx)
          (hc.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) (norm_nonneg _)))
      _ ≤ C * max 1 ‖x‖ := by
        rw [← add_mul]
        apply mul_le_mul_of_nonneg_right _ (zero_le_one.trans hx)
        dsimp [C]
        linarith
  apply max_le
  · exact (hC.trans (le_mul_of_one_le_right (by positivity : 0 ≤ C) hx))
  apply max_le
  · exact (norm_add_le _ _).trans hbound
  · exact (norm_sub_le _ _).trans hbound

private theorem integrable_columnOrbitWord (R : G →* (E →L[ℂ] E)) (hR : IsContinuousRepresentation R)
    (μ : Measure X) [μ.IsAddHaarMeasure] (F : 𝓢(X, ℂ)) (v : D R) (s : List Mat) :
    Integrable (fun x => derivativeCLM I R s (F x • representation I R (j x) v)) μ := by
  let p : Seminorm ℂ (D R) := wordSeminormFamily I R s
  have hp : Continuous p := (derivativeCLM I R s).continuous.norm
  obtain ⟨k, q, _, hq⟩ := exists_seminorm_le_unitHeight_pow ℝ n R hR p hp
  let C : ℝ := 1 + ‖(1 : Mat)‖ + ‖columnCLM (r := r) (d := d)‖
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hcont : Continuous (fun x => representation I R (j x) v) :=
    (continuous_representation_units R hR).comp ((continuous_zeroRowColumnUnipotent r d).prodMk continuous_const)
  have hB := ((F.integrable (μ := μ)).norm.add (F.integrable_pow_mul μ k)).const_mul (C ^ k * q v)
  refine hB.mono' ((derivativeCLM I R s).continuous.comp (F.continuous.smul hcont)).aestronglyMeasurable
    (ae_of_all _ fun x => ?_)
  rw [map_smul, norm_smul]
  change ‖F x‖ * p (representation I R (j x) v) ≤ (C ^ k * q v) * (‖F x‖ + ‖x‖ ^ k * ‖F x‖)
  have hmax : (max 1 ‖x‖) ^ k ≤ 1 + ‖x‖ ^ k := by
    rcases le_total (1 : ℝ) ‖x‖ with h | h
    · rw [max_eq_right h]
      exact le_add_of_nonneg_left zero_le_one
    · rw [max_eq_left h, one_pow]
      exact le_add_of_nonneg_right (by positivity)
  have hheight : unitHeight (j x) ^ k ≤ C ^ k * (1 + ‖x‖ ^ k) := by
    calc
      _ ≤ (C * max 1 ‖x‖) ^ k := pow_le_pow_left₀ (zero_le_one.trans (one_le_unitHeight _))
        (unitHeight_column_le (d := d) x) k
      _ ≤ _ := by rw [mul_pow]; gcongr
  calc
    _ ≤ ‖F x‖ * ((C ^ k * (1 + ‖x‖ ^ k)) * q v) :=
      mul_le_mul_of_nonneg_left ((hq (j x) v).trans (mul_le_mul_of_nonneg_right hheight (apply_nonneg _ _)))
        (norm_nonneg _)
    _ = _ := by ring

/-- Multiplying a real smooth Whittaker coefficient by a Schwartz function of
its leading-block last row is realized by a single smooth vector. -/
def RealSmoothRowAbsorptionStatement : Prop :=
  ∀ (r d : ℕ) (E : Type u) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (R : Langlands.GeneralLinear (r + (d + 1) + 1) ℝ →* (E →L[ℂ] E)),
    let model := matrixModel ℝ (r + (d + 1) + 1)
    let V := DerivativeSmoothVectors model R
    IsContinuousRepresentation R →
    ∀ (a : ℝˣ) (L : V →L[ℂ] ℂ),
      (∀ (u : Langlands.GeneralLinear.upperUnipotent (r + (d + 1) + 1) ℝ) (v : V),
        L (representation model R u.val v) = realWhittakerCharacter a u.val * L v) →
      ∀ (v : V) (Φ : 𝓢((Fin (r + 1) → ℝ), ℂ)), ∃ w : V,
        ∀ g : Langlands.GeneralLinear (r + 1) ℝ,
          L (representation model R (appendIdentity r (d + 1) g) w) =
            L (representation model R (appendIdentity r (d + 1) g) v) * Φ (lastRow g)

theorem realSmoothRowAbsorption : RealSmoothRowAbsorptionStatement.{u} := by
  intro r d E _ _ _ R model V hR a L hL v Φ
  let column := zeroRowColumnUnipotent (F := ℝ) r d
  let F := RealGodement.realRowSchwartzFourier (r + 1) (-a) Φ
  let μ := rowMeasure (realSelfDualMeasure a) (r + 1)
  let : (realSelfDualMeasure a).measure.IsAddHaarMeasure := (realSelfDualMeasure a).isAddHaar
  let : SigmaFinite (realSelfDualMeasure a).measure := inferInstance
  let : μ.IsAddHaarMeasure := rowMeasure_isAddHaar _ _
  obtain ⟨w, _, hw⟩ := smoothWordIntegral R μ hR (fun x => F x • representation model R (column x) v)
    (integrable_columnOrbitWord R hR μ F v)
  refine ⟨w, fun g => ?_⟩
  let b := appendIdentity r (d + 1) g
  let W := L (representation model R b v)
  let Lb := L.comp (SmoothAction.derivativeAction model R b)
  have hpt (x : Fin (r + 1) → ℝ) : Lb (F x • representation model R (column x) v) =
      (F x * (realScaledCharacter a).complex (∑ i, x i * lastRow g i)) * W := by
    rw [map_smul, smul_eq_mul]
    change F x * L (representation model R b (representation model R (column x) v)) = _
    unfold column b
    rw [← Module.End.mul_apply, ← map_mul, appendIdentity_mul_zeroRowColumnUnipotent,
      map_mul, Module.End.mul_apply]
    let z := g.val *ᵥ x
    let u : Langlands.GeneralLinear.upperUnipotent (r + (d + 1) + 1) ℝ :=
      ⟨column z, zeroRowColumnUnipotent_mem_upperUnipotent r d z⟩
    change F x * L (representation model R u.val (representation model R b v)) = _
    rw [hL, realWhittakerCharacter, show u.val = zeroRowColumnUnipotent r d z from rfl,
      zeroRowColumnUnipotent_superdiagonal_sum]
    have hz : z (Fin.last r) = ∑ i, x i * lastRow g i := by
      change (∑ i : Fin (r + 1), g.val (Fin.last r) i * x i) = _
      exact Finset.sum_congr rfl fun i _ => mul_comm (g.val (Fin.last r) i) (x i)
    rw [hz, mul_assoc]
  change Lb w = W * Φ (lastRow g)
  calc
    Lb w = ∫ x, Lb (F x • representation model R (column x) v) ∂μ := (hw Lb).2
    _ = ∫ x, (F x * (realScaledCharacter a).complex (∑ i, x i * lastRow g i)) * W ∂μ :=
      integral_congr_ae (ae_of_all _ hpt)
    _ = W * realFourierTransform a F (lastRow g) := by
      rw [integral_mul_const]
      exact mul_comm _ W
    _ = W * Φ (lastRow g) := by
      rw [← RealGodement.realRowSchwartzFourier_apply,
        show RealGodement.realRowSchwartzFourier (r + 1) a F = Φ by
          simpa only [neg_neg, F] using RealGodement.realRowSchwartzFourier_neg_comp (r + 1) (-a) Φ]

end Langlands.Global.RankinSelbergGlobal.RealSmoothRowAbsorption
