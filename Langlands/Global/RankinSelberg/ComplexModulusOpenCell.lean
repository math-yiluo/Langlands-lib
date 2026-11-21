import Langlands.Global.RankinSelberg.ComplexJacquetChamberConvergence
import Langlands.Representation.Archimedean.ComplexJacquetLimit

/-! # Compact integration in full opposite-unipotent coordinates -/

noncomputable section
open MeasureTheory Filter Set
open scoped Classical Matrix Matrix.Norms.Operator Langlands.Archimedean.ComplexDuality

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexModulusOpenCell

open Langlands.Archimedean (principalSeries unitaryCompact)
open Langlands.Archimedean.ComplexKIntegralInvariance (modulusCharacter)
open Langlands.Archimedean.ComplexDuality (unitaryHaar)
open Langlands.Archimedean.ComplexJacquetLimit (isPhasePower_modulus iotaGL_mul_chartGL)
open Langlands.Archimedean.ComplexPartialJacquet (IsStrictlyDominant vecMulEquiv vecMulEquiv_apply map_vecMulEquiv)
open Langlands.Archimedean.ComplexMaximalParabolicIntegration (chartGL chartConstant chartConstant_pos
  natural integral_eq_chart leviSlice leviSlice_mem JGL_val Jmat iotaGL iotaGL_val
  det_upperUnipotent normSqC normSqC_det_unitary normSqC_one)
open Langlands.GeneralLinear (upperUnipotent inverseTranspose inverseTranspose_coe continuous_inverseTranspose
  UpperEntryPair upperEntryCoordinates upperEntryProductMeasure weylLong weylLong_mul_self)
open Langlands.HarmonicAnalysis (AdditiveHaarMeasure rowMeasure)
open Langlands.Shahidi (lastColumnUpper upperLeftUnipotent unipotentProduct
  integrable_unipotentProductMeasure_iff integral_unipotentProductMeasure)
open ComplexJacquetChamberConvergence (complexJacquetOpenCellConvergence)
open ComplexJacquetUnipotentMeasure (entryHaar entryHaar_sigmaFinite transposeReflection transposeReflection_eq
  measurePreserving_transposeReflection unipotentProductMeasure_entryHaar)

local instance modulusOpenCellNMeasurable (m : ℕ) : MeasurableSpace (upperUnipotent m ℂ) := borel _
local instance modulusOpenCellNBorel (m : ℕ) : BorelSpace (upperUnipotent m ℂ) := ⟨rfl⟩

local notation "G" => fun m => Langlands.GeneralLinear m ℂ
local notation "N" => fun m => upperUnipotent m ℂ

private def scalarLebesgue : AdditiveHaarMeasure ℂ := ⟨volume, inferInstance, inferInstance⟩

/-- Product Haar on the upper unipotent with the scalar complex Lebesgue measure. -/
def complexEntryLebesgue (m : ℕ) : Measure (N m) := entryHaar scalarLebesgue m

private theorem rowMeasure_scalarLebesgue (m : ℕ) : rowMeasure scalarLebesgue m = (volume : Measure (Fin m → ℂ)) := by
  rw [volume_pi]
  rfl

attribute [simp] groupTranspose_val

private theorem groupTranspose_lastColumn {m : ℕ} (v : Fin m → ℂ) :
    groupTranspose (lastColumnUpper v).val = chartGL v := by
  apply Units.ext
  rw [groupTranspose_val, chartGL, JGL_val]
  ext i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp [Jmat, lastColumnUpper, Matrix.transpose_apply, Matrix.one_apply, Fin.castSucc_ne_last, eq_comm]

private theorem groupTranspose_upperLeft {m : ℕ} (u : N m) :
    groupTranspose (upperLeftUnipotent u).val = iotaGL (groupTranspose u.val) := by
  apply Units.ext
  rw [groupTranspose_val, iotaGL_val, groupTranspose_val]
  ext i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;> simp

private theorem groupTranspose_product {m : ℕ} (u : N m) (v : Fin m → ℂ) :
    groupTranspose (unipotentProduct (u, v)).val = chartGL v * iotaGL (groupTranspose u.val) := by
  change groupTranspose ((upperLeftUnipotent u).val * (lastColumnUpper v).val) = _
  rw [groupTranspose_mul, groupTranspose_lastColumn, groupTranspose_upperLeft]

private theorem det_groupTranspose_unipotent {m : ℕ} (u : N m) :
    (groupTranspose u.val).val.det = 1 := by
  rw [groupTranspose_val, Matrix.det_transpose, det_upperUnipotent]

private theorem integrable_modulus_transpose {m : ℕ} {F : G (m + 1) → ℂ}
    (hF : F ∈ principalSeries ℂ (m + 1) (modulusCharacter (m + 1))) :
    Integrable (fun u : N (m + 1) => F (groupTranspose u.val)) (complexEntryLebesgue (m + 1)) := by
  let n := m + 1
  let w := weylLong n ℂ
  have hd : IsStrictlyDominant (fun i : ℕ => ((n : ℂ) - 1) / 2 - (i : ℂ)) m := by
    intro i hi
    push_cast
    simp only [Complex.sub_re, Complex.add_re, Complex.one_re, Complex.natCast_re]
    linarith
  have hi := complexJacquetOpenCellConvergence m scalarLebesgue (modulusCharacter n) _
    (isPhasePower_modulus n) hd F hF w
  refine ((measurePreserving_transposeReflection scalarLebesgue n).integrable_comp_of_integrable hi).congr
    (ae_of_all _ fun u => ?_)
  change F (w * (transposeReflection n u).val * w) = F (groupTranspose u.val)
  rw [transposeReflection_eq, Whittaker.reflectedUnipotent_val, Subgroup.coe_inv]
  change F (w * (w * groupTranspose u.val * w) * w) = _
  congr 1
  have hw : w * w = 1 := weylLong_mul_self n ℂ
  calc
    _ = (w * w) * groupTranspose u.val * (w * w) := by simp only [mul_assoc]
    _ = _ := by rw [hw, one_mul, mul_one]

private theorem measurePreserving_chartReorder {m : ℕ} :
    MeasurePreserving (fun p : N m × (Fin m → ℂ) => (p.1, p.2 ᵥ* (groupTranspose p.1.val)⁻¹.val))
      ((complexEntryLebesgue m).prod volume) ((complexEntryLebesgue m).prod volume) := by
  let : SigmaFinite (complexEntryLebesgue m) := entryHaar_sigmaFinite scalarLebesgue m
  apply (MeasurePreserving.id (complexEntryLebesgue m)).skew_product
    (g := fun (u : N m) (v : Fin m → ℂ) => v ᵥ* (groupTranspose u.val)⁻¹.val)
  · apply Continuous.measurable
    exact continuous_snd.matrix_vecMul (Units.continuous_val.comp
      ((continuous_groupTranspose.comp (continuous_subtype_val.comp continuous_fst)).inv))
  · apply ae_of_all
    intro u
    let e := vecMulEquiv ((groupTranspose u.val)⁻¹).det_ne_zero
    have he : (e : (Fin m → ℂ) → (Fin m → ℂ)) = fun v => v ᵥ* (groupTranspose u.val)⁻¹.val := rfl
    rw [← he, map_vecMulEquiv]
    have hd : (groupTranspose u.val)⁻¹.val.det = 1 := by
      have hmul := congrArg Matrix.det (Units.mul_inv (groupTranspose u.val))
      simpa only [Matrix.det_mul, Matrix.det_one, det_groupTranspose_unipotent, one_mul] using hmul
    rw [hd]
    simp

private theorem integral_transpose_step {m : ℕ} {F : G (m + 1) → ℂ}
    (hF : F ∈ principalSeries ℂ (m + 1) (modulusCharacter (m + 1))) :
    (∫ v : Fin m → ℂ, ∫ u : N m, F (iotaGL (groupTranspose u.val) * chartGL v) ∂complexEntryLebesgue m) =
      ∫ u : N (m + 1), F (groupTranspose u.val) ∂complexEntryLebesgue (m + 1) := by
  let : SigmaFinite (complexEntryLebesgue m) := entryHaar_sigmaFinite scalarLebesgue m
  let L (u : N (m + 1)) := F (groupTranspose u.val)
  let Ψ (p : N m × (Fin m → ℂ)) := F (chartGL p.2 * iotaGL (groupTranspose p.1.val))
  have hm : complexEntryLebesgue (m + 1) = Langlands.Shahidi.unipotentProductMeasure
      (complexEntryLebesgue m) (volume : Measure (Fin m → ℂ)) := by
    rw [complexEntryLebesgue, complexEntryLebesgue, ← rowMeasure_scalarLebesgue,
      unipotentProductMeasure_entryHaar]
  have hΨ (p : N m × (Fin m → ℂ)) : L (unipotentProduct p) = Ψ p := by
    rcases p with ⟨u, v⟩
    exact congrArg F (groupTranspose_product u v)
  have hi : Integrable Ψ ((complexEntryLebesgue m).prod volume) := by
    have hI : Integrable L (complexEntryLebesgue (m + 1)) := integrable_modulus_transpose hF
    rw [hm] at hI
    exact ((integrable_unipotentProductMeasure_iff _ _ _).mp hI).congr (ae_of_all _ hΨ)
  let Ψ' (p : N m × (Fin m → ℂ)) := F (iotaGL (groupTranspose p.1.val) * chartGL p.2)
  let σ (p : N m × (Fin m → ℂ)) := (p.1, p.2 ᵥ* (groupTranspose p.1.val)⁻¹.val)
  have he : Ψ ∘ σ = Ψ' := funext fun p => congrArg F (iotaGL_mul_chartGL _ _).symm
  have hi' : Integrable Ψ' ((complexEntryLebesgue m).prod volume) :=
    he ▸ measurePreserving_chartReorder.integrable_comp_of_integrable hi
  calc
    _ = ∫ p, Ψ' p ∂(complexEntryLebesgue m).prod volume := (integral_prod_symm _ hi').symm
    _ = ∫ p, Ψ p ∂(complexEntryLebesgue m).prod volume := by
      rw [← he]
      have hs := measurePreserving_chartReorder (m := m)
      have ha : AEStronglyMeasurable Ψ (((complexEntryLebesgue m).prod volume).map σ) :=
        hs.map_eq.symm ▸ hi.aestronglyMeasurable
      exact (integral_map hs.measurable.aemeasurable ha).symm.trans (by rw [hs.map_eq])
    _ = _ := by
      rw [hm, integral_unipotentProductMeasure]
      exact integral_congr_ae (ae_of_all _ fun p => (hΨ p).symm)

private theorem entryLebesgue_zero_univ : complexEntryLebesgue 0 univ = 1 := by
  let : IsEmpty (UpperEntryPair 0) := ⟨fun p => Fin.elim0 p.1.1⟩
  rw [complexEntryLebesgue, entryHaar,
    Measure.map_apply (upperEntryCoordinates (K := ℂ) 0).symm.measurable MeasurableSet.univ,
    preimage_univ, upperEntryProductMeasure, Measure.pi_univ, Finset.prod_of_isEmpty]

/-- Compact integration of a modulus-equivariant section is integration of its restriction to
transposed upper unipotent matrices, up to a positive constant depending only on the rank. -/
def ComplexModulusOpenCellStatement : Prop :=
  ∀ m : ℕ, ∃ c : ℝ, 0 < c ∧ ∀ F : G m → ℂ,
    F ∈ principalSeries ℂ m (modulusCharacter m) →
    Integrable (fun u : N m => F (groupTranspose u.val)) (complexEntryLebesgue m) ∧
    (∫ k : unitaryCompact ℂ m, F k.val ∂unitaryHaar m) =
      (c : ℂ) * ∫ u : N m, F (groupTranspose u.val) ∂complexEntryLebesgue m

set_option maxHeartbeats 1100000 in
theorem complexModulusOpenCell : ComplexModulusOpenCellStatement := by
  intro m
  induction m with
  | zero =>
    refine ⟨1, zero_lt_one, fun F _ => ?_⟩
    let : Subsingleton (G 0) := ⟨fun g h => Units.ext (Matrix.ext fun i _ => Fin.elim0 i)⟩
    let : IsFiniteMeasure (complexEntryLebesgue 0) := ⟨by rw [entryLebesgue_zero_univ]; exact ENNReal.one_lt_top⟩
    simp only [Subsingleton.elim (a := _) (b := (1 : G 0))]
    refine ⟨integrable_const _, ?_⟩
    rw [integral_const, integral_const, probReal_univ, Measure.real, entryLebesgue_zero_univ]
    simp
  | succ m ih =>
    obtain ⟨c, hc, ih⟩ := ih
    refine ⟨chartConstant m * c, mul_pos (chartConstant_pos m) hc, fun F hF =>
      ⟨integrable_modulus_transpose hF, ?_⟩⟩
    have hnat (v : Fin m → ℂ) : natural F (chartGL v) =
        (c : ℂ) * ∫ u : N m, F (iotaGL (groupTranspose u.val) * chartGL v) ∂complexEntryLebesgue m := by
      have h := (ih (leviSlice F (chartGL v)) (leviSlice_mem hF _)).2
      simpa only [natural, leviSlice, normSqC_det_unitary, det_groupTranspose_unipotent, normSqC_one,
        inv_one, mul_one] using h
    rw [integral_eq_chart hF]
    simp_rw [hnat]
    rw [integral_const_mul, integral_transpose_step hF, Complex.ofReal_mul, mul_assoc]

end Langlands.Global.RankinSelbergGlobal.ComplexModulusOpenCell
