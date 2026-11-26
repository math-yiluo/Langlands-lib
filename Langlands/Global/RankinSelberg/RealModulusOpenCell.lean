import Langlands.Global.RankinSelberg.RealGodementOpenCellConvergence
import Langlands.Global.RankinSelberg.RealJacquetUnipotentMeasure
import Langlands.Representation.Archimedean.JacquetLimit

/-! # Compact integration in full opposite-unipotent coordinates over the real field -/

noncomputable section
open MeasureTheory Filter Set
open scoped Classical Matrix Matrix.Norms.Operator Manifold ContDiff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealModulusOpenCell

open Langlands.Archimedean (principalSeries unitaryCompact)
open Langlands.Archimedean.RealPrincipalSeriesDuality (haarK)
open Langlands.Archimedean.MaximalParabolicIntegration (modulusCharacter IsModulusCovariant
  chartGL chartConstant chartConstant_pos natural integral_eq_chart leviSlice leviSlice_covariant
  contMDiff_leviSlice JGL_val Jmat iotaGL iotaGL_val det_upperUnipotent abs_det_unitary)
open Langlands.Archimedean.JacquetLimit (iotaGL_mul_chartGL)
open Langlands.Archimedean.PartialJacquet (vecMulEquiv vecMulEquiv_apply map_vecMulEquiv)
open Langlands.GeneralLinear (inverseTranspose inverseTranspose_coe
  continuous_inverseTranspose UpperEntryPair upperEntryCoordinates upperEntryProductMeasure
  weylLong weylLong_mul_self)
open Langlands.HarmonicAnalysis (AdditiveHaarMeasure rowMeasure)
open Langlands.LocalFactor.Archimedean (realStandardMeasure)
open Langlands.Shahidi (lastColumnUpper upperLeftUnipotent unipotentProduct
  integrable_unipotentProductMeasure_iff integral_unipotentProductMeasure)
open RealJacquetUnipotentMeasure (entryHaar entryHaar_sigmaFinite transposeReflection
  transposeReflection_eq measurePreserving_transposeReflection unipotentProductMeasure_entryHaar)

local instance realModulusOpenCellNMeasurable (m : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear.upperUnipotent m ℝ) := borel _
local instance realModulusOpenCellNBorel (m : ℕ) : BorelSpace (Langlands.GeneralLinear.upperUnipotent m ℝ) := ⟨rfl⟩
local instance realModulusOpenCellKMeasurable (m : ℕ) :
    MeasurableSpace (unitaryCompact ℝ m) := borel _
local instance realModulusOpenCellKBorel (m : ℕ) : BorelSpace (unitaryCompact ℝ m) := ⟨rfl⟩

local notation "G" => fun m => Langlands.GeneralLinear m ℝ
local notation "N" => fun m => Langlands.GeneralLinear.upperUnipotent m ℝ

/-- Transpose of an invertible real matrix. -/
def groupTranspose {m : ℕ} (g : Langlands.GeneralLinear m ℝ) : Langlands.GeneralLinear m ℝ :=
  inverseTranspose m ℝ g⁻¹

@[simp]
theorem groupTranspose_val {m : ℕ} (g : Langlands.GeneralLinear m ℝ) :
    (groupTranspose g).val = g.val.transpose := by
  rw [groupTranspose, inverseTranspose_coe, inv_inv]

theorem continuous_groupTranspose {m : ℕ} :
    Continuous (groupTranspose (m := m)) :=
  (continuous_inverseTranspose m ℝ).comp continuous_inv

theorem groupTranspose_mul {m : ℕ} (g h : Langlands.GeneralLinear m ℝ) :
    groupTranspose (g * h) = groupTranspose h * groupTranspose g := by
  simp only [groupTranspose, mul_inv_rev, map_mul]

/-- Product Haar on the upper unipotent with the scalar real Lebesgue measure. -/
def realEntryLebesgue (m : ℕ) : Measure (N m) := entryHaar realStandardMeasure m

theorem realEntryLebesgue_sigmaFinite (m : ℕ) : SigmaFinite (realEntryLebesgue m) :=
  entryHaar_sigmaFinite realStandardMeasure m

private theorem rowMeasure_standard (m : ℕ) :
    rowMeasure realStandardMeasure m = (volume : Measure (Fin m → ℝ)) := by
  rw [volume_pi]
  rfl

private theorem selfDualOne_measure :
    (Langlands.Global.RankinSelbergGlobal.ArchimedeanLocal.realSelfDualMeasure 1).measure =
      realStandardMeasure.measure := by
  change ((NNReal.sqrt ‖((1 : ℝˣ) : ℝ)‖₊) • (volume : Measure ℝ)) = volume
  simp

private theorem upperStepHaar_one (t : ℕ) :
    RealGodement.upperStepHaar t 1 = realEntryLebesgue (t + 1) := by
  change (upperEntryProductMeasure
      (Langlands.Global.RankinSelbergGlobal.ArchimedeanLocal.realSelfDualMeasure 1) (t + 1)).map
      (upperEntryCoordinates (t + 1)).symm =
    (upperEntryProductMeasure realStandardMeasure (t + 1)).map (upperEntryCoordinates (t + 1)).symm
  congr 1
  unfold upperEntryProductMeasure
  rw [selfDualOne_measure]

private theorem groupTranspose_lastColumn {m : ℕ} (v : Fin m → ℝ) :
    groupTranspose (lastColumnUpper v).val = chartGL v := by
  apply Units.ext
  rw [groupTranspose_val, chartGL, JGL_val]
  ext i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp [Jmat, lastColumnUpper, Matrix.transpose_apply, Matrix.one_apply, Fin.castSucc_ne_last,
      eq_comm]

private theorem groupTranspose_upperLeft {m : ℕ} (u : N m) :
    groupTranspose (upperLeftUnipotent u).val = iotaGL (groupTranspose u.val) := by
  apply Units.ext
  rw [groupTranspose_val, iotaGL_val, groupTranspose_val]
  ext i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp [Langlands.Archimedean.MaximalParabolicIntegration.iota]

private theorem groupTranspose_product {m : ℕ} (u : N m) (v : Fin m → ℝ) :
    groupTranspose (unipotentProduct (u, v)).val =
      chartGL v * iotaGL (groupTranspose u.val) := by
  change groupTranspose ((upperLeftUnipotent u).val * (lastColumnUpper v).val) = _
  rw [groupTranspose_mul, groupTranspose_lastColumn, groupTranspose_upperLeft]

private theorem det_groupTranspose_unipotent {m : ℕ} (u : N m) :
    (groupTranspose u.val).val.det = 1 := by
  rw [groupTranspose_val, Matrix.det_transpose, det_upperUnipotent]

private theorem norm_modulusCharacter (n : ℕ) (d : Fin n → ℝˣ) :
    ‖modulusCharacter n d‖ =
      ∏ l : Fin n, |(d l : ℝ)| ^ (((n : ℝ) - 1) - 2 * ((l : ℕ) : ℝ)) := by
  rw [modulusCharacter, norm_prod]
  refine Finset.prod_congr rfl fun l _ => ?_
  have h : (((n : ℂ) - 1) - 2 * ((l : ℕ) : ℂ)) = ((((n : ℝ) - 1) - 2 * ((l : ℕ) : ℝ) : ℝ) : ℂ) := by
    push_cast; ring
  rw [h, Complex.norm_cpow_eq_rpow_re_of_pos (abs_pos.mpr (d l).ne_zero), Complex.ofReal_re]

private theorem integrable_modulus_transpose {m : ℕ} {F : G (m + 1) → ℂ}
    (hFc : Continuous F) (hF : IsModulusCovariant F) :
    Integrable (fun u : N (m + 1) => F (groupTranspose u.val)) (realEntryLebesgue (m + 1)) := by
  let w := weylLong (m + 1) ℝ
  have hi := RealGodement.realGodementOpenCellConvergence m 1 F (modulusCharacter (m + 1))
    (fun l : ℕ => ((m : ℝ) + 1 - 1) - 2 * (l : ℝ)) hFc (fun d u k => hF d u k)
    (fun d => by
      rw [norm_modulusCharacter]
      refine Finset.prod_congr rfl fun l _ => ?_
      push_cast; ring_nf)
    (fun j _ => by push_cast; linarith) w
  rw [upperStepHaar_one] at hi
  have hc : Continuous (fun u : N (m + 1) => F (w * u.val * w)) :=
    hFc.comp ((continuous_const.mul continuous_subtype_val).mul continuous_const)
  have hn : Integrable (fun u : N (m + 1) => F (w * u.val * w)) (realEntryLebesgue (m + 1)) := by
    refine hi.norm.mono' hc.aestronglyMeasurable (ae_of_all _ fun u => le_of_eq ?_)
    simp only [RealGodement.additiveJacquetKernel, norm_mul,
      Langlands.Whittaker.norm_standardCharacter, mul_one]
    rfl
  refine ((measurePreserving_transposeReflection realStandardMeasure (m + 1)).integrable_comp_of_integrable
    hn).congr (ae_of_all _ fun u => ?_)
  change F (w * (transposeReflection (m + 1) u).val * w) = F (groupTranspose u.val)
  rw [transposeReflection_eq, Whittaker.reflectedUnipotent_val, Subgroup.coe_inv]
  change F (w * (w * groupTranspose u.val * w) * w) = _
  congr 1
  have hw : w * w = 1 := weylLong_mul_self (m + 1) ℝ
  calc
    _ = (w * w) * groupTranspose u.val * (w * w) := by simp only [mul_assoc]
    _ = _ := by rw [hw, one_mul, mul_one]

private theorem measurePreserving_chartReorder {m : ℕ} :
    MeasurePreserving (fun p : N m × (Fin m → ℝ) => (p.1, p.2 ᵥ* (groupTranspose p.1.val)⁻¹.val))
      ((realEntryLebesgue m).prod volume) ((realEntryLebesgue m).prod volume) := by
  let : SigmaFinite (realEntryLebesgue m) := realEntryLebesgue_sigmaFinite m
  apply (MeasurePreserving.id (realEntryLebesgue m)).skew_product
    (g := fun (u : N m) (v : Fin m → ℝ) => v ᵥ* (groupTranspose u.val)⁻¹.val)
  · apply Continuous.measurable
    exact continuous_snd.matrix_vecMul (Units.continuous_val.comp
      ((continuous_groupTranspose.comp (continuous_subtype_val.comp continuous_fst)).inv))
  · apply ae_of_all
    intro u
    let e := vecMulEquiv ((groupTranspose u.val)⁻¹).det_ne_zero
    have he : (e : (Fin m → ℝ) → (Fin m → ℝ)) = fun v => v ᵥ* (groupTranspose u.val)⁻¹.val := by
      funext v; exact vecMulEquiv_apply _ v
    rw [← he, map_vecMulEquiv]
    have hd : (groupTranspose u.val)⁻¹.val.det = 1 := by
      have hmul := congrArg Matrix.det (Units.mul_inv (groupTranspose u.val))
      simpa only [Matrix.det_mul, Matrix.det_one, det_groupTranspose_unipotent, one_mul] using hmul
    rw [hd]
    simp

private theorem integral_transpose_step {m : ℕ} {F : G (m + 1) → ℂ}
    (hFc : Continuous F) (hF : IsModulusCovariant F) :
    (∫ v : Fin m → ℝ, ∫ u : N m, F (iotaGL (groupTranspose u.val) * chartGL v)
        ∂realEntryLebesgue m) =
      ∫ u : N (m + 1), F (groupTranspose u.val) ∂realEntryLebesgue (m + 1) := by
  let : SigmaFinite (realEntryLebesgue m) := realEntryLebesgue_sigmaFinite m
  let L (u : N (m + 1)) := F (groupTranspose u.val)
  let Ψ (p : N m × (Fin m → ℝ)) := F (chartGL p.2 * iotaGL (groupTranspose p.1.val))
  have hm : realEntryLebesgue (m + 1) = Langlands.Shahidi.unipotentProductMeasure
      (realEntryLebesgue m) (volume : Measure (Fin m → ℝ)) := by
    rw [realEntryLebesgue, realEntryLebesgue, ← rowMeasure_standard,
      unipotentProductMeasure_entryHaar]
  have hΨ (p : N m × (Fin m → ℝ)) : L (unipotentProduct p) = Ψ p := by
    rcases p with ⟨u, v⟩
    exact congrArg F (groupTranspose_product u v)
  have hi : Integrable Ψ ((realEntryLebesgue m).prod volume) := by
    have hI : Integrable L (realEntryLebesgue (m + 1)) := integrable_modulus_transpose hFc hF
    rw [hm] at hI
    exact ((integrable_unipotentProductMeasure_iff _ _ _).mp hI).congr (ae_of_all _ hΨ)
  let Ψ' (p : N m × (Fin m → ℝ)) := F (iotaGL (groupTranspose p.1.val) * chartGL p.2)
  let σ (p : N m × (Fin m → ℝ)) := (p.1, p.2 ᵥ* (groupTranspose p.1.val)⁻¹.val)
  have he : Ψ ∘ σ = Ψ' := funext fun p => congrArg F (iotaGL_mul_chartGL _ _).symm
  have hi' : Integrable Ψ' ((realEntryLebesgue m).prod volume) :=
    he ▸ measurePreserving_chartReorder.integrable_comp_of_integrable hi
  calc
    _ = ∫ p, Ψ' p ∂(realEntryLebesgue m).prod volume := (integral_prod_symm _ hi').symm
    _ = ∫ p, Ψ p ∂(realEntryLebesgue m).prod volume := by
      rw [← he]
      have hs := measurePreserving_chartReorder (m := m)
      have ha : AEStronglyMeasurable Ψ (((realEntryLebesgue m).prod volume).map σ) :=
        hs.map_eq.symm ▸ hi.aestronglyMeasurable
      exact (integral_map hs.measurable.aemeasurable ha).symm.trans (by rw [hs.map_eq])
    _ = _ := by
      rw [hm, integral_unipotentProductMeasure]
      exact integral_congr_ae (ae_of_all _ fun p => (hΨ p).symm)

private theorem entryLebesgue_zero_univ : realEntryLebesgue 0 univ = 1 := by
  let : IsEmpty (UpperEntryPair 0) := ⟨fun p => Fin.elim0 p.1.1⟩
  rw [realEntryLebesgue, entryHaar,
    Measure.map_apply (upperEntryCoordinates (K := ℝ) 0).symm.measurable MeasurableSet.univ,
    preimage_univ, upperEntryProductMeasure, Measure.pi_univ, Finset.prod_of_isEmpty]

private theorem haarK_zero_univ : haarK 0 univ = 1 := by
  rw [Langlands.Archimedean.RealPrincipalSeriesDuality.haarK]
  exact Measure.haarMeasure_self

/-- Compact integration of a smooth modulus-covariant function is integration of its
restriction to transposed upper unipotent matrices, up to a positive constant depending only on
the rank. -/
def RealModulusOpenCellStatement : Prop :=
  ∀ m : ℕ, ∃ c : ℝ, 0 < c ∧ ∀ F : G m → ℂ,
    ContMDiff (Langlands.Archimedean.matrixModel ℝ m) 𝓘(ℝ, ℂ) ∞ F → IsModulusCovariant F →
    Integrable (fun u : N m => F (groupTranspose u.val)) (realEntryLebesgue m) ∧
    (∫ k : unitaryCompact ℝ m, F k.val ∂haarK m) =
      (c : ℂ) * ∫ u : N m, F (groupTranspose u.val) ∂realEntryLebesgue m

set_option maxHeartbeats 1100000 in
theorem realModulusOpenCell : RealModulusOpenCellStatement := by
  intro m
  induction m with
  | zero =>
    refine ⟨1, zero_lt_one, fun F _ _ => ?_⟩
    let : Subsingleton (G 0) := ⟨fun g h => Units.ext (Matrix.ext fun i _ => Fin.elim0 i)⟩
    let : IsFiniteMeasure (realEntryLebesgue 0) :=
      ⟨by rw [entryLebesgue_zero_univ]; exact ENNReal.one_lt_top⟩
    let : IsProbabilityMeasure (haarK 0) := ⟨haarK_zero_univ⟩
    simp only [Subsingleton.elim (a := _) (b := (1 : G 0))]
    refine ⟨integrable_const _, ?_⟩
    rw [integral_const, integral_const, probReal_univ, Measure.real, entryLebesgue_zero_univ]
    simp
  | succ m ih =>
    obtain ⟨c, hc, ih⟩ := ih
    refine ⟨chartConstant m * c, mul_pos (chartConstant_pos m) hc, fun F hFs hF =>
      ⟨integrable_modulus_transpose hFs.continuous hF, ?_⟩⟩
    have hnat (v : Fin m → ℝ) : natural F (chartGL v) =
        (c : ℂ) * ∫ u : N m, F (iotaGL (groupTranspose u.val) * chartGL v)
          ∂realEntryLebesgue m := by
      have h := (ih (leviSlice F (chartGL v)) (contMDiff_leviSlice hFs _)
        (leviSlice_covariant hF _)).2
      simpa only [natural, leviSlice, abs_det_unitary, det_groupTranspose_unipotent, abs_one,
        Complex.ofReal_one, inv_one, mul_one] using h
    rw [integral_eq_chart hFs hF]
    simp_rw [hnat]
    rw [integral_const_mul, integral_transpose_step hFs.continuous hF, Complex.ofReal_mul,
      mul_assoc]

end Langlands.Global.RankinSelbergGlobal.RealModulusOpenCell
