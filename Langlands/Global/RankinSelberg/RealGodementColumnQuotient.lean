import Langlands.Global.RankinSelberg.RealGodementColumnConvergence
import Langlands.Global.RankinSelberg.RealGodementStepFubini
import Langlands.Global.RankinSelberg.RealGodementWeil
import Langlands.Global.RankinSelberg.RealGodementKernelDescent

/-! # From the real Godement first-column integral to the quotient kernel -/

noncomputable section

open Langlands.GeneralLinear Langlands.HarmonicAnalysis Langlands.LocalFactor.Archimedean
open Langlands.Global.RankinSelbergGlobal.ArchimedeanLocal Langlands.Whittaker
open Langlands.RankinSelberg (LeftUnipotentQuotient)
open Langlands.QuotientIntegration
open MeasureTheory MeasureTheory.Measure Matrix
open scoped Matrix.Norms.Operator SchwartzMap NNReal ENNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGodement

private local instance (d : ℕ) : MeasurableSpace (Langlands.GeneralLinear (d + 1) ℝ) := borel _
private local instance (d : ℕ) : BorelSpace (Langlands.GeneralLinear (d + 1) ℝ) := ⟨rfl⟩
private local instance (d : ℕ) : MeasurableSpace (GeneralLinear.upperUnipotent (d + 1) ℝ) := borel _
private local instance (d : ℕ) : BorelSpace (GeneralLinear.upperUnipotent (d + 1) ℝ) := ⟨rfl⟩
private local instance (d : ℕ) : MeasurableSpace (LeftUnipotentQuotient d ℝ) := borel _
private local instance (d : ℕ) : BorelSpace (LeftUnipotentQuotient d ℝ) := ⟨rfl⟩

variable {t : ℕ}

local notation "m" => (t + 1)
local notation "G" => Langlands.GeneralLinear (t + 1) ℝ
local notation "H" => Langlands.GeneralLinear (t + 2) ℝ
local notation "N" => GeneralLinear.upperUnipotent (t + 1) ℝ
local notation "Q" => LeftUnipotentQuotient t ℝ
local notation "V" => (Fin (t + 1) → ℝ)
local notation "M" => Matrix (Fin (t + 1)) (Fin (t + 1)) ℝ
local notation "X" => Matrix (Fin (t + 1)) (Fin (t + 2)) ℝ

/-- The iterated Godement group integrand before taking the first-column Fourier transform. -/
def stepGroupIntegrand (a : ℝˣ) (Φ : 𝓢(X, ℂ)) (W : G → ℂ) (c : RealCharacterData)
    (g : H) (h : G) : ℂ :=
  determinantWeight c ((m : ℂ) / 2) g * stepColumnSlice a Φ h g 1 * W (columnRepresentative h) *
    determinantWeight c (((t + 2 : ℕ) : ℂ) / 2) h

private theorem stepColumnSlice_eq_fourier (a : ℝˣ) (Φ : 𝓢(X, ℂ)) (h : G) (g : H) (A : M) :
    stepColumnSlice a Φ h g A = ((|h.val.det|⁻¹ : ℝ) : ℂ) *
      firstColumnFourier a (rectangularTranslate 1 g Φ) (columnFrequency h) (h.val * A) := by
  simpa only [stepColumnSlice, rectangularTranslate_apply, Units.val_one, Matrix.one_mul,
    dotProduct_single_one, columnFrequency] using
    firstColumnFourier_mul a (rectangularTranslate 1 g Φ) h (Pi.single 0 1) A

private theorem detWeight_column (c : RealCharacterData) (h : G) :
    ((|h.val.det|⁻¹ : ℝ) : ℂ) * determinantWeight c (((t + 2 : ℕ) : ℂ) / 2) h =
      (((h.val.det / |h.val.det| : ℝ) : ℂ) ^ c.parity.val) *
        Complex.exp ((c.exponent + (t : ℂ) / 2) * (Real.log |h.val.det| : ℂ)) := by
  let b : ℂ := ((|h.val.det| : ℝ) : ℂ)
  have hb : b ≠ 0 := Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr (determinant h).ne_zero)
  rw [Complex.ofReal_inv]
  change b⁻¹ * ((c.character (determinant h) : ℂ) * b ^ (((t + 2 : ℕ) : ℂ) / 2)) = _
  rw [c.character_eq]
  change b⁻¹ * ((_ * b ^ c.exponent) * b ^ (((t + 2 : ℕ) : ℂ) / 2)) = _
  rw [show (((t + 2 : ℕ) : ℂ) / 2) = (t : ℂ) / 2 + 1 by push_cast; ring,
    Complex.cpow_add _ _ hb, Complex.cpow_one]
  rw [show (determinant h : ℝ) = h.val.det from rfl]
  calc
    _ = (((h.val.det / |h.val.det| : ℝ) : ℂ) ^ c.parity.val) *
        (b ^ c.exponent * b ^ ((t : ℂ) / 2)) * (b * b⁻¹) := by ring
    _ = _ := by
      rw [mul_inv_cancel₀ hb, mul_one, ← Complex.cpow_add _ _ hb,
        Complex.cpow_def_of_ne_zero hb, ← Complex.ofReal_log (abs_nonneg h.val.det), mul_comm (Real.log _ : ℂ)]

/-- The exact conversion to the first-column Mellin integrand, including the determinant Jacobian. -/
theorem stepGroupIntegrand_eq_columnMellin (a : ℝˣ) (Φ : 𝓢(X, ℂ)) (W : G → ℂ)
    (c : RealCharacterData) (g : H) (h : G) :
    stepGroupIntegrand a Φ W c g h = determinantWeight c ((m : ℂ) / 2) g *
      columnMellinIntegrand a (rectangularTranslate 1 g Φ) W c.parity.val (c.exponent + (t : ℂ) / 2) h := by
  rw [stepGroupIntegrand, stepColumnSlice_eq_fourier, Matrix.mul_one]
  calc
    _ = determinantWeight c ((m : ℂ) / 2) g *
        (firstColumnFourier a (rectangularTranslate 1 g Φ) (columnFrequency h) h.val * W (columnRepresentative h)) *
        (((|h.val.det|⁻¹ : ℝ) : ℂ) * determinantWeight c (((t + 2 : ℕ) : ℂ) / 2) h) := by ring
    _ = _ := by rw [detWeight_column, columnMellinIntegrand, columnMellinBase]; ring

private theorem conjugate_det (u : N) :
    determinant (weylLong m ℝ * u.val * weylLong m ℝ) = 1 := by
  have hu : determinant u.val = 1 := Units.ext (Langlands.RankinSelberg.unipotent_det u)
  rw [map_mul, map_mul, hu, mul_one, ← map_mul, weylLong_mul_self, map_one]

private theorem conjugate_frequency (u : N) :
    columnFrequency (weylLong m ℝ * u.val * weylLong m ℝ) = Pi.single 0 1 := by
  have hInv : (weylLong m ℝ * u.val * weylLong m ℝ)⁻¹ =
      weylLong m ℝ * (u⁻¹).val * weylLong m ℝ := by
    simp only [_root_.mul_inv_rev, weylLong_inv, Subgroup.coe_inv, mul_assoc]
  funext i
  rw [columnFrequency, inverseTranspose_coe, hInv]
  simp only [Matrix.mulVec, dotProduct_single_one, Matrix.transpose_apply]
  rw [weylLong_conjugate_entry]
  by_cases hi : i = 0
  · subst i
    simp only [UpperUnipotent.entry_diag, Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne hi]
    exact UpperUnipotent.entry_eq_zero _ (Fin.rev_lt_rev.mpr (Fin.pos_iff_ne_zero.mpr hi))

private theorem stepColumnSlice_conjugate (a : ℝˣ) (Φ : 𝓢(X, ℂ)) (h : G) (g : H) (u : N) :
    stepColumnSlice a Φ (h * (weylLong m ℝ * u.val * weylLong m ℝ)) g 1 =
      stepColumnSlice a Φ h g (weylLong m ℝ * u.val * weylLong m ℝ).val := by
  let v := weylLong m ℝ * u.val * weylLong m ℝ
  let Ψ := rectangularTranslate h g Φ
  have hv : v.val.det = 1 := congrArg Units.val (conjugate_det u)
  have hFourier := firstColumnFourier_mul a Ψ v (Pi.single 0 1) 1
  rw [show (inverseTranspose m ℝ v).val *ᵥ Pi.single 0 1 = Pi.single 0 1 from conjugate_frequency u,
    Matrix.mul_one, hv, abs_one, inv_one, Complex.ofReal_one, one_mul, firstColumnFourier_apply] at hFourier
  unfold stepColumnSlice
  calc
    _ = ∫ x, Ψ (v.val * joinFirstColumn x 1) *
        (realScaledCharacter a).complex (x ⬝ᵥ Pi.single 0 1) ∂rowMeasure (realSelfDualMeasure a) m := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        simp only [Ψ, v, rectangularTranslate_apply, Units.val_mul, Matrix.mul_assoc,
          dotProduct_single_one]
    _ = _ := by
      simpa only [Ψ, v, rectangularTranslate_apply, dotProduct_single_one] using hFourier

private theorem columnRepresentative_inverse_mul_weyl (k : G) :
    columnRepresentative (k⁻¹ * weylLong m ℝ) = k := by
  simp only [columnRepresentative, _root_.mul_inv_rev, weylLong_inv, inv_inv, ← mul_assoc,
    weylLong_mul_self, one_mul]

/-- In the inverse unipotent coordinate the orbit integrand has the positive standard character. -/
private theorem stepGroupIntegrand_orbit (a : ℝˣ) (Φ : 𝓢(X, ℂ)) (W : G → ℂ)
    (hW : KernelWhittakerLaw a W) (c : RealCharacterData) (g : H) (k : G) (u : N) :
    let h := k⁻¹ * weylLong m ℝ
    stepGroupIntegrand a Φ W c g (((u⁻¹).val * k)⁻¹ * weylLong m ℝ) =
      (determinantWeight c ((m : ℂ) / 2) g * W k *
        determinantWeight c (((t + 2 : ℕ) : ℂ) / 2) h) *
      (stepColumnSlice a Φ h g (weylLong m ℝ * u.val * weylLong m ℝ).val *
        (standardCharacter (realScaledCharacter a) t u : ℂ)) := by
  let h := k⁻¹ * weylLong m ℝ
  let v := weylLong m ℝ * u.val * weylLong m ℝ
  have hRep : ((u⁻¹).val * k)⁻¹ * weylLong m ℝ = h * v := by
    simp only [h, v, _root_.mul_inv_rev, Subgroup.coe_inv, inv_inv, mul_assoc]
    rw [← mul_assoc (weylLong m ℝ), weylLong_mul_self, one_mul]
  have hWeight : determinantWeight c (((t + 2 : ℕ) : ℂ) / 2) (h * v) =
      determinantWeight c (((t + 2 : ℕ) : ℂ) / 2) h := by
    have hv : determinant v = 1 := conjugate_det u
    have hDet : Matrix.GeneralLinearGroup.det (h * v) = determinant h := by
      change determinant (h * v) = determinant h
      rw [map_mul, hv, mul_one]
    simp only [determinantWeight, MonoidHom.comp_apply, hDet]
  dsimp only
  unfold stepGroupIntegrand
  rw [columnRepresentative_inverse_mul_weyl, hRep, hWeight, stepColumnSlice_conjugate,
    hW u⁻¹ k, standardCharacter_realScaled_neg, map_inv, inv_inv]
  ring

private theorem unipotentHaar_invInvariant (D : RealQuotientMeasureData t) :
    D.unipotentHaar.IsInvInvariant := by
  let e := upperEntryCoordinates m (K := ℝ)
  let : LocallyCompactSpace N := e.isClosedEmbedding.locallyCompactSpace
  let : SecondCountableTopology N := e.secondCountableTopology
  let : D.unipotentHaar.IsHaarMeasure := D.unipotentHaar_isHaar
  let : D.unipotentHaar.IsMulRightInvariant := D.unipotentHaar_rightInvariant
  have hMod (u : N) : modularCharacter u = 1 := by
    change modularCharacterFun u = 1
    rw [modularCharacterFun_eq_haarScalarFactor D.unipotentHaar]
    have hSelf (ν : Measure N) [ν.IsHaarMeasure] (he : ν = D.unipotentHaar) :
        haarScalarFactor ν D.unipotentHaar = 1 := by
      subst ν
      exact haarScalarFactor_self _
    exact hSelf _ (map_mul_right_eq_self D.unipotentHaar u)
  have h := (Langlands.Haar.haarInversionDensity N D.unipotentHaar).1
  have he : (fun u : N => (modularCharacter u : ℝ≥0∞)) = 1 := funext fun u => by
    rw [hMod, ENNReal.coe_one]
    rfl
  rw [he, withDensity_one] at h
  exact ⟨h⟩

private theorem exists_unipotentHaar_eq_stepHaar (a : ℝˣ) (D : RealQuotientMeasureData t) :
    ∃ scale : ℝ≥0, 0 < scale ∧ D.unipotentHaar = scale • upperStepHaar t a := by
  let e := upperEntryCoordinates m (K := ℝ)
  let : LocallyCompactSpace N := e.isClosedEmbedding.locallyCompactSpace
  let : SecondCountableTopology N := e.secondCountableTopology
  let : D.unipotentHaar.IsHaarMeasure := D.unipotentHaar_isHaar
  let : (upperStepHaar t a).IsHaarMeasure := upperStepHaar_isHaar t a
  exact ⟨haarScalarFactor D.unipotentHaar (upperStepHaar t a),
    haarScalarFactor_pos_of_isHaarMeasure _ _, isMulLeftInvariant_eq_smul _ _⟩

/-- The actual uniform Whittaker model satisfies the law used for the quotient kernel. -/
theorem kernelWhittakerLaw_of_mem_model {a : ℝˣ} {ds : List RealBlock} {W : G → ℂ}
    (hW : W ∈ realUniformWhittakerModel t ds (-a)) : KernelWhittakerLaw a W := by
  intro u k
  exact (RealUniformWhittaker.iteratedRightDerivative_mem_regularFunctions hW []).1 u.val u.property k

private theorem columnQuotient (a : ℝˣ) (D : RealQuotientMeasureData t) (scale : ℝ≥0) (hscale : 0 < scale)
    (hμ : D.unipotentHaar = scale • upperStepHaar t a) (Φ : 𝓢(X, ℂ)) (ds : List RealBlock) (W : G → ℂ)
    (c : RealCharacterData) (g : H) (hW : W ∈ realUniformWhittakerModel t ds (-a)) :
    Integrable (stepGroupIntegrand a Φ W c g) D.groupHaar ∧
    Integrable (quotientKernel a Φ W (kernelWhittakerLaw_of_mem_model hW) c g) D.measure ∧
    determinantWeight c ((m : ℂ) / 2) g *
      (∫ h, columnMellinIntegrand a (rectangularTranslate 1 g Φ) W c.parity.val (c.exponent + (t : ℂ) / 2) h
        ∂D.groupHaar) =
      (scale : ℂ) * ∫ q, quotientKernel a Φ W (kernelWhittakerLaw_of_mem_model hW) c g q ∂D.measure := by
  let : D.groupHaar.IsHaarMeasure := D.groupHaar_isHaar
  let : D.unipotentHaar.IsMulRightInvariant := D.unipotentHaar_rightInvariant
  let : D.unipotentHaar.IsInvInvariant := unipotentHaar_invInvariant D
  let law := kernelWhittakerLaw_of_mem_model hW
  let K := quotientKernel a Φ W law c g
  let f := stepGroupIntegrand a Φ W c g
  let J := columnMellinIntegrand a (rectangularTranslate 1 g Φ) W c.parity.val (c.exponent + (t : ℂ) / 2)
  let d := determinantWeight c ((m : ℂ) / 2) g
  have hJ : Integrable J D.groupHaar :=
    (columnMellin_convergence_of_mem_model D.groupHaar a (rectangularTranslate 1 g Φ) hW c.parity.val).1 _
  have hf : Integrable f D.groupHaar :=
    (hJ.const_mul d).congr (Filter.Eventually.of_forall fun h => (stepGroupIntegrand_eq_columnMellin a Φ W c g h).symm)
  have hSym := realMatrixHaar_symmetries D.groupHaar
  let : D.groupHaar.IsMulRightInvariant := hSym.1
  let : D.groupHaar.IsInvInvariant := hSym.2
  let e := (MeasurableEquiv.inv G).trans (Homeomorph.mulRight (weylLong m ℝ)).toMeasurableEquiv
  let F := f ∘ e
  have he : MeasurePreserving e D.groupHaar D.groupHaar :=
    (measurePreserving_mul_right D.groupHaar (weylLong m ℝ)).comp (measurePreserving_inv D.groupHaar)
  have hWeil := (realGodementWeil t D F (he.integrable_comp_of_integrable hf)).2
  have hOrbit (q : Q) : quotientAverage N D.unipotentHaar F q = (scale : ℂ) * K q := by
    induction q using Quotient.inductionOn with
    | h k =>
      rw [quotientAverage_mk]
      let h := k⁻¹ * weylLong m ℝ
      let weight := d * W k * determinantWeight c (((t + 2 : ℕ) : ℂ) / 2) h
      let I : N → ℂ := fun u => stepColumnSlice a Φ h g (weylLong m ℝ * u.val * weylLong m ℝ).val *
        (standardCharacter (realScaledCharacter a) t u : ℂ)
      calc
        _ = ∫ u : N, F ((u⁻¹).val * k) ∂D.unipotentHaar := (integral_inv_eq_self _ D.unipotentHaar).symm
        _ = ∫ u, weight * I u ∂D.unipotentHaar :=
          integral_congr_ae (Filter.Eventually.of_forall (stepGroupIntegrand_orbit a Φ W law c g k))
        _ = _ := by
          rw [hμ, integral_smul_nnreal_measure, integral_const_mul]
          change (scale : ℝ) • (weight * ∫ u, I u ∂upperStepHaar t a) =
            (scale : ℂ) * K (Quotient.mk _ k)
          rw [Complex.real_smul, ← (realGodementStepFubini t a Φ h g).2]
          change _ = (scale : ℂ) * kernelIntegrand a Φ W c g k
          unfold kernelIntegrand
          simp only [weight, d, h, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
          rw [add_assoc (t : ℂ) 1 1, show (1 : ℂ) + 1 = 2 by norm_num]
          ac_rfl
  have hScaled : Integrable (fun q => (scale : ℂ) * K q) D.measure :=
    hWeil.1.congr (Filter.Eventually.of_forall hOrbit)
  have hUnit : IsUnit (scale : ℂ) := isUnit_iff_ne_zero.mpr (by exact_mod_cast hscale.ne')
  refine ⟨hf, (integrable_const_mul_iff hUnit K).mp hScaled, ?_⟩
  change d * (∫ h, J h ∂D.groupHaar) = (scale : ℂ) * ∫ q, K q ∂D.measure
  calc
    _ = ∫ h, f h ∂D.groupHaar := by
      rw [← integral_const_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall fun h => (stepGroupIntegrand_eq_columnMellin a Φ W c g h).symm)
    _ = ∫ k, F k ∂D.groupHaar := (he.integral_comp' f).symm
    _ = ∫ q, quotientAverage N D.unipotentHaar F q ∂D.measure := hWeil.2.symm
    _ = _ := by
      rw [← integral_const_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall hOrbit)

/-- Equations (7.7) and (7.8) agree with the precise comparison of the
supplied subgroup Haar and the self-dual entry-product Haar. Both outer
integrands are absolutely integrable. -/
def RealGodementColumnQuotientStatement : Prop :=
  ∀ (d : ℕ) (a : ℝˣ) (D : RealQuotientMeasureData d),
    ∃ scale : ℝ≥0, 0 < scale ∧ D.unipotentHaar = scale • upperStepHaar d a ∧
      ∀ (Φ : 𝓢(Matrix (Fin (d + 1)) (Fin (d + 2)) ℝ, ℂ)) (ds : List RealBlock)
        (W : Langlands.GeneralLinear (d + 1) ℝ → ℂ) (c : RealCharacterData)
        (g : Langlands.GeneralLinear (d + 2) ℝ) (hW : W ∈ realUniformWhittakerModel d ds (-a)),
        Integrable (stepGroupIntegrand a Φ W c g) D.groupHaar ∧
        Integrable (quotientKernel a Φ W (kernelWhittakerLaw_of_mem_model hW) c g) D.measure ∧
        determinantWeight c (((d : ℂ) + 1) / 2) g *
          (∫ h, columnMellinIntegrand a (rectangularTranslate 1 g Φ) W c.parity.val (c.exponent + (d : ℂ) / 2) h
            ∂D.groupHaar) =
          (scale : ℂ) * ∫ q, quotientKernel a Φ W (kernelWhittakerLaw_of_mem_model hW) c g q ∂D.measure

theorem realGodementColumnQuotient : RealGodementColumnQuotientStatement := by
  intro d a D
  obtain ⟨scale, hscale, hμ⟩ := exists_unipotentHaar_eq_stepHaar a D
  exact ⟨scale, hscale, hμ, columnQuotient a D scale hscale hμ⟩

end Langlands.Global.RankinSelbergGlobal.RealGodement
