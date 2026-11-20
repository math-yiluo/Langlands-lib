import Langlands.Global.RankinSelberg.RealGodementOpenCellConvergence
import Langlands.Global.RankinSelberg.RealLocalWhittakerModel

/-! # Whittaker covariance of the real open-cell Jacquet integral -/

noncomputable section

open Langlands.Archimedean Langlands.GeneralLinear Langlands.HarmonicAnalysis Langlands.Whittaker
open Langlands.LocalFactor.Archimedean
open Langlands.Global.RankinSelbergGlobal.ArchimedeanLocal
open MeasureTheory
open scoped BigOperators Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGodement

open PartialJacquet

private local instance (n : ℕ) : MeasurableSpace (GeneralLinear.upperUnipotent n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (GeneralLinear.upperUnipotent n ℝ) := ⟨rfl⟩

private theorem rightCoordinateCorrection_depends {n : ℕ} (v : GeneralLinear.upperUnipotent n ℝ)
    (ij : UpperEntryPair n) (X Y : UpperEntryPair n → ℝ)
    (h : ∀ kl : UpperEntryPair n,
      kl.1.2.val - kl.1.1.val < ij.1.2.val - ij.1.1.val → X kl = Y kl) :
    (upperEntryCoordinates n ((upperEntryCoordinates n).symm X * v) - X) ij =
      (upperEntryCoordinates n ((upperEntryCoordinates n).symm Y * v) - Y) ij := by
  simp only [Pi.sub_apply, upperEntryCoordinates_mul, Homeomorph.apply_symm_apply]
  have hs :
      (∑ k : {k : Fin n // ij.1.1 < k ∧ k < ij.1.2},
        X ⟨(ij.1.1, k), k.2.1⟩ * upperEntryCoordinates n v ⟨(k, ij.1.2), k.2.2⟩) =
      ∑ k : {k : Fin n // ij.1.1 < k ∧ k < ij.1.2},
        Y ⟨(ij.1.1, k), k.2.1⟩ * upperEntryCoordinates n v ⟨(k, ij.1.2), k.2.2⟩ := by
    apply Finset.sum_congr rfl
    intro k _
    rw [h ⟨(ij.1.1, k), k.2.1⟩]
    have hi : ij.1.1.val < k.val.val := k.2.1
    have hj : k.val.val < ij.1.2.val := k.2.2
    dsimp
    omega
  rw [hs]
  abel

/-- Right multiplication preserves the real upper-entry Haar measure. -/
theorem upperStepHaar_isMulRightInvariant (t : ℕ) (a : ℝˣ) :
    (upperStepHaar t a).IsMulRightInvariant := by
  let n := t + 1
  let e := upperEntryCoordinates n (K := ℝ)
  let μ := upperEntryProductMeasure (realSelfDualMeasure a) n
  refine ⟨fun v => ?_⟩
  let changeCoordinates := fun X : UpperEntryPair n → ℝ => e (e.symm X * v)
  let correction := fun X : UpperEntryPair n → ℝ => changeCoordinates X - X
  have hContinuous : Continuous correction :=
    (e.continuous.comp (e.symm.continuous.mul continuous_const)).sub continuous_id
  have hp := finiteTriangularTranslation (UpperEntryPair n) (fun _ => ℝ)
    (fun _ => (realSelfDualMeasure a).measure) (fun ij => ij.1.2.val - ij.1.1.val)
    correction hContinuous.measurable (rightCoordinateCorrection_depends v)
  have hCorrection : (fun X ij => correction X ij + X ij) = changeCoordinates :=
    funext fun X => funext fun ij => sub_add_cancel _ _
  rw [hCorrection] at hp
  have hMap : Measure.map changeCoordinates μ = μ := hp.map_eq
  have hTransport : (fun u => u * v) ∘ e.symm = e.symm ∘ changeCoordinates := by
    funext X
    simp only [Function.comp_apply, changeCoordinates, Homeomorph.symm_apply_apply]
  have hRight : Measurable (fun u => u * v) := (continuous_id.mul continuous_const).measurable
  change Measure.map (fun u => u * v) (μ.map e.symm) = μ.map e.symm
  rw [Measure.map_map hRight e.symm.measurable, hTransport,
    ← Measure.map_map e.symm.measurable hp.measurable, hMap]

variable {t : ℕ}

local notation "G" => Langlands.GeneralLinear (t + 1) ℝ
local notation "N" => GeneralLinear.upperUnipotent (t + 1) ℝ

/-- The integral commutes with right translations of the inducing function. -/
theorem additiveJacquetIntegral_rightTranslate (a : ℝˣ) (f : G → ℂ) (g h : G) :
    additiveJacquetIntegral a (fun x => f (x * h)) g = additiveJacquetIntegral a f (g * h) := by
  simp only [additiveJacquetIntegral, additiveJacquetKernel, mul_assoc]

private theorem additiveJacquetIntegral_covariance (a : ℝˣ) (f : G → ℂ) (v : N) (g : G) :
    additiveJacquetIntegral a f (v.val * g) =
      realWhittakerCharacter (-a) v.val * additiveJacquetIntegral a f g := by
  let : (upperStepHaar t a).IsMulRightInvariant := upperStepHaar_isMulRightInvariant t a
  let w := weylLong (t + 1) ℝ
  let ψ := standardCharacter (realScaledCharacter a) t
  let c := realWhittakerCharacter (-a) v.val
  have hc : c * (ψ v : ℂ) = 1 := by
    let s := ∑ i : Fin t, v.val.val i.castSucc i.succ
    change realStandardCharacter.complex (((-a : ℝˣ) : ℝ) * s) *
      realStandardCharacter.complex ((a : ℝ) * s) = 1
    rw [← AddChar.map_add_eq_mul, Units.val_neg, neg_mul, neg_add_cancel]
    exact realStandardCharacter.complex.map_zero_eq_one
  have hpoint (u : N) : additiveJacquetKernel a f (v.val * g) u =
      c * additiveJacquetKernel a f g (u * v) := by
    change f (w * u.val * (v.val * g)) * (ψ u : ℂ) =
      c * (f (w * (u * v).val * g) * (ψ (u * v) : ℂ))
    simp only [Subgroup.coe_mul, map_mul, Units.val_mul, mul_assoc]
    calc
      _ = f (w * (u.val * (v.val * g))) * (ψ u : ℂ) * (c * (ψ v : ℂ)) := by rw [hc, mul_one]
      _ = _ := by ring
  unfold additiveJacquetIntegral
  rw [← integral_const_mul]
  calc
    _ = ∫ u : N, (fun u => c * additiveJacquetKernel a f g u) (u * v) ∂upperStepHaar t a :=
      integral_congr_ae (ae_of_all _ hpoint)
    _ = _ := integral_mul_right_eq_self (μ := upperStepHaar t a)
      (fun u : N => c * additiveJacquetKernel a f g u) v

/-- With the positive phase, the Jacquet integral is covariant under left upper
unipotent multiplication for the negative additive parameter. -/
def RealGodementOpenCellCovarianceStatement : Prop :=
  ∀ (t : ℕ) (a : ℝˣ) (f : Langlands.GeneralLinear (t + 1) ℝ → ℂ)
    (v : GeneralLinear.upperUnipotent (t + 1) ℝ) (g : Langlands.GeneralLinear (t + 1) ℝ),
    additiveJacquetIntegral a f (v.val * g) =
      realWhittakerCharacter (-a) v.val * additiveJacquetIntegral a f g

theorem realGodementOpenCellCovariance : RealGodementOpenCellCovarianceStatement :=
  fun _ => additiveJacquetIntegral_covariance

/-- The family of convergent Jacquet integrals is linear in a dominant
signed-power principal-series vector. -/
def additiveJacquetLinear (a : ℝˣ) {χ : ℕ → ℝˣ → ℂ} {e : ℕ → ℂ}
    (hχ : IsSignedPower χ e) (he : IsStrictlyDominant e t) :
    principalSeries ℝ (t + 1) χ →ₗ[ℂ] (G → ℂ) where
  toFun f := additiveJacquetIntegral a f
  map_add' f f' := by
    funext g
    have hf := integrable_additiveJacquetKernel_of_mem_principalSeries a hχ he f.property g
    have hf' := integrable_additiveJacquetKernel_of_mem_principalSeries a hχ he f'.property g
    change additiveJacquetIntegral a (fun k => f.val k + f'.val k) g =
      additiveJacquetIntegral a f g + additiveJacquetIntegral a f' g
    unfold additiveJacquetIntegral
    rw [← integral_add hf hf']
    exact integral_congr_ae (ae_of_all _ fun u => by simp only [additiveJacquetKernel, add_mul])
  map_smul' z f := by
    funext g
    change additiveJacquetIntegral a (fun k => z * f.val k) g = z * additiveJacquetIntegral a f g
    simp only [additiveJacquetIntegral, additiveJacquetKernel, mul_assoc, integral_const_mul]

end Langlands.Global.RankinSelbergGlobal.RealGodement
