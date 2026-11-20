import Langlands.Analysis.CompactLinearParameterIntegralProof
import Langlands.Global.RankinSelberg.ComplexGodementJacquetComparison
import Langlands.Global.RankinSelberg.ComplexJacquetChamberConvergence
import Langlands.Representation.Archimedean.ComplexStrictLanglandsQuotient
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Smoothness of the complex open-cell Jacquet integral in the strict chamber -/

noncomputable section

open MeasureTheory
open scoped ContDiff ENNReal Manifold Matrix.Norms.Operator Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquetChamberSmooth

open Langlands.Archimedean
open Langlands.Archimedean.ComplexGramFormula (complexPositionExponent)
open Langlands.Archimedean.ComplexPartialJacquet (IsStrictlyDominant norm_principalSeriesCharacter)
open Langlands.Archimedean.ComplexStrictLanglandsQuotient (isPhasePower)
open Langlands.GeneralLinear (weylLong)
open Langlands.HarmonicAnalysis (AdditiveHaarMeasure)
open Langlands.LocalFactor.Archimedean (ComplexCharacterData complexScaledCharacter)
open ComplexGodementJacquetComparison (openCellIntegral)
open ComplexJacquetUnipotentMeasure (entryHaar entryHaar_sigmaFinite)
open ComplexJacquetChamberConvergence (radialChar sphericalMajorant sphericalMajorant_mem
  complexJacquetOpenCellConvergence)
open ComplexLocalIwasawa (alpha continuous_alpha kpart continuous_kpart npart
  conjTorus conjTorus_val logTorus_neg npart_mul_logTorus_mul_kpart)
open ComplexLocalWhittakerGauge (logTorus)

attribute [local instance] ArchimedeanLocal.archimedeanComplexGLMeasurable
  ArchimedeanLocal.archimedeanComplexGLBorel ArchimedeanLocal.archimedeanComplexNMeasurable
  ArchimedeanLocal.archimedeanComplexNBorel

open scoped Langlands.Archimedean.ComplexDuality

variable {r : ℕ}
local notation "G" => Langlands.GeneralLinear (r + 1) ℂ
local notation "N" => GeneralLinear.upperUnipotent (r + 1) ℂ
local notation "K" => unitaryCompact ℂ (r + 1)
local notation "Mat" => Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ
local notation "w" => weylLong (r + 1) ℂ
private abbrev Phase := {z : ℂ // z ∈ Metric.sphere (0 : ℂ) 1}
local notation "Y" => K × Phase

private def expUnits (y : Fin (r + 1) → ℝ) (i : Fin (r + 1)) : ℂˣ :=
  Units.mk0 (Real.exp (y i) : ℂ) (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _))

private theorem continuous_expUnits (i : Fin (r + 1)) : Continuous (fun y => expUnits y i) := by
  rw [Units.continuous_iff]
  constructor
  · exact Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_apply i))
  · change Continuous (fun y : Fin (r + 1) → ℝ => (Real.exp (y i) : ℂ)⁻¹)
    simp_rw [← Complex.ofReal_inv, ← Real.exp_neg]
    exact Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_apply i).neg)

private def borelScalar (χ : ℕ → ℂˣ → ℂ) (x : G) : ℂ :=
  principalSeriesCharacter ℂ (r + 1) χ (expUnits (alpha x))

private theorem apply_mul_eq_borelScalar {χ : ℕ → ℂˣ → ℂ}
    {f : G → ℂ} (hf : f ∈ principalSeries ℂ (r + 1) χ) (x g : G) :
    f (x * g) = borelScalar χ x * f ((kpart x).val * g) := by
  let y := alpha x
  let u := conjTorus (-y) (npart x)
  have hx : logTorus y * u.val * (kpart x).val = x := by
    change logTorus y * (conjTorus (-y) (npart x)).val * (kpart x).val = _
    rw [conjTorus_val, logTorus_neg, inv_inv]
    calc
      _ = (npart x).val * logTorus y * (kpart x).val := by group
      _ = x := npart_mul_logTorus_mul_kpart x
  have he := hf.2 (expUnits y) u ((kpart x).val * g)
  change f (logTorus y * u.val * ((kpart x).val * g)) = _ at he
  rwa [← mul_assoc, hx] at he

private theorem continuous_positionCharacter (ds : List ComplexCharacterData) (i : ℕ) :
    Continuous (complexPositionCharacter ds i) := by
  induction ds generalizing i with
  | nil => exact continuous_const
  | cons d ds ih =>
    cases i with
    | zero => exact Units.continuous_val.comp d.character.continuous
    | succ i => exact ih i

private theorem continuous_borelScalar (ds : List ComplexCharacterData) :
    Continuous (borelScalar (r := r) (complexPositionCharacter ds)) := by
  unfold borelScalar principalSeriesCharacter
  apply continuous_finsetProd _ fun i _ => ?_
  have ht := (continuous_expUnits (r := r) i).comp continuous_alpha
  refine ((continuous_positionCharacter ds i).comp ht).mul ?_
  refine (Complex.continuous_ofReal.comp ((Units.continuous_val.comp ht).norm.pow _)).cpow
    continuous_const fun x => ?_
  exact Complex.ofReal_mem_slitPlane.mpr (pow_pos (norm_pos_iff.mpr (expUnits (alpha x) i).ne_zero) _)

private theorem radialPhasePower (t : ℕ → ℝ) :
    ComplexPartialJacquet.IsPhasePower (radialChar t) (fun i => (t i : ℂ)) where
  eq := by intro l z; simp [radialChar, ComplexGramFormula.norm_phaseUnit]
  one := by intro l; simp [radialChar]
  norm_phase := by intro l z; simp [radialChar, ComplexGramFormula.norm_phaseUnit]

private theorem norm_borelScalar_eq (ds : List ComplexCharacterData) (x : G) :
    ‖borelScalar (complexPositionCharacter ds) x‖ =
      ‖sphericalMajorant (r + 1) (fun i => (complexPositionExponent ds i).re) x‖ := by
  let t : ℕ → ℝ := fun i => (complexPositionExponent ds i).re
  have hs := apply_mul_eq_borelScalar (sphericalMajorant_mem (r + 1) t).1 x 1
  have hk : sphericalMajorant (r + 1) t (kpart x).val = 1 := by
    let κ : Matrix.unitaryGroup (Fin (r + 1)) ℂ := ⟨(kpart x).val.val, (kpart x).2⟩
    have hκ : Unitary.toUnits κ = (kpart x).val := Units.ext rfl
    rw [← hκ, sphericalMajorant, ComplexPrincipalSeriesExtension.extension_unitary]
  rw [mul_one, mul_one, hk, mul_one] at hs
  rw [hs]
  simp only [borelScalar, norm_principalSeriesCharacter (isPhasePower ds),
    norm_principalSeriesCharacter (radialPhasePower t), Complex.ofReal_re, t]

private def coefficient (ds : List ComplexCharacterData) (a : ℂˣ) (u : N) : ℂ :=
  borelScalar (complexPositionCharacter ds) (w * u.val) * complexWhittakerCharacter a u.val

private theorem continuous_coefficient (ds : List ComplexCharacterData) (a : ℂˣ) :
    Continuous (coefficient (r := r) ds a) := by
  refine ((continuous_borelScalar ds).comp (continuous_const.mul continuous_subtype_val)).mul ?_
  unfold complexWhittakerCharacter
  exact (complexScaledCharacter a).continuous_complex.comp
    (continuous_finsetSum _ fun i _ => (GeneralLinear.UpperUnipotent.entry i.castSucc i.succ).continuous)

private theorem coefficient_ne_zero (ds : List ComplexCharacterData) (a : ℂˣ) (u : N) :
    coefficient ds a u ≠ 0 := by
  apply mul_ne_zero
  · unfold borelScalar principalSeriesCharacter
    refine Finset.prod_ne_zero_iff.mpr (fun i _ => mul_ne_zero ((isPhasePower ds).ne_zero _ _) ?_)
    exact Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr
      (pow_ne_zero _ (norm_ne_zero_iff.mpr (expUnits (alpha (w * u.val)) i).ne_zero))))
  · exact norm_ne_zero_iff.mp (by simp [complexWhittakerCharacter])

private theorem integrable_coefficient (μ : AdditiveHaarMeasure ℂ) (ds : List ComplexCharacterData)
    (a : ℂˣ) (he : IsStrictlyDominant (complexPositionExponent ds) r) :
    Integrable (coefficient ds a) (entryHaar μ (r + 1)) := by
  let t : ℕ → ℝ := fun i => (complexPositionExponent ds i).re
  have hdom : IsStrictlyDominant (fun i => (t i : ℂ)) r := by
    simpa only [IsStrictlyDominant, Complex.ofReal_re, t] using he
  have h := complexJacquetOpenCellConvergence r μ _ _ (radialPhasePower t) hdom _
    (sphericalMajorant_mem (r + 1) t).1 1
  refine h.norm.mono' (continuous_coefficient ds a).aestronglyMeasurable (ae_of_all _ fun u => ?_)
  unfold coefficient
  rw [norm_mul, show ‖complexWhittakerCharacter a u.val‖ = 1 by simp [complexWhittakerCharacter],
    mul_one, norm_borelScalar_eq, mul_one]

private def unitPhase (ds : List ComplexCharacterData) (a : ℂˣ) (u : N) : Phase :=
  ⟨coefficient ds a u / (‖coefficient ds a u‖ : ℂ), by
    rw [mem_sphere_zero_iff_norm, norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
      div_self (norm_ne_zero_iff.mpr (coefficient_ne_zero ds a u))]⟩

private def compactCoordinates (ds : List ComplexCharacterData) (a : ℂˣ) (u : N) : Y :=
  (kpart (w * u.val), unitPhase ds a u)

private theorem continuous_compactCoordinates (ds : List ComplexCharacterData) (a : ℂˣ) :
    Continuous (compactCoordinates (r := r) ds a) := by
  refine (continuous_kpart.comp (continuous_const.mul continuous_subtype_val)).prodMk ?_
  exact ((continuous_coefficient ds a).div
    (Complex.continuous_ofReal.comp (continuous_coefficient ds a).norm)
    (fun u => Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (coefficient_ne_zero ds a u)))).subtype_mk _

private def compactMeasure (μ : AdditiveHaarMeasure ℂ) (ds : List ComplexCharacterData)
    (a : ℂˣ) : Measure Y :=
  ((entryHaar μ (r + 1)).withDensity (fun u => ‖coefficient ds a u‖ₑ)).map (compactCoordinates ds a)

private theorem compactMeasure_finite (μ : AdditiveHaarMeasure ℂ) (ds : List ComplexCharacterData)
    (a : ℂˣ) (he : IsStrictlyDominant (complexPositionExponent ds) r) :
    IsFiniteMeasure (compactMeasure (r := r) μ ds a) := by
  have h := (hasFiniteIntegral_iff_enorm.mp (integrable_coefficient μ ds a he).2)
  have : IsFiniteMeasure ((entryHaar μ (r + 1)).withDensity (fun u => ‖coefficient ds a u‖ₑ)) :=
    ⟨by rwa [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]⟩
  unfold compactMeasure
  infer_instance

private theorem openCellIntegral_compact (μ : AdditiveHaarMeasure ℂ) (ds : List ComplexCharacterData)
    (a : ℂˣ) {f : G → ℂ} (hf : f ∈ complexStandardModule (r + 1) ds) (g : G) :
    openCellIntegral a (entryHaar μ (r + 1)) f g =
      ∫ p : Y, (p.2 : ℂ) * f (p.1.val * g) ∂compactMeasure μ ds a := by
  have : SigmaFinite (entryHaar μ (r + 1)) := entryHaar_sigmaFinite μ (r + 1)
  unfold compactMeasure openCellIntegral
  rw [integral_map (continuous_compactCoordinates ds a).measurable.aemeasurable]
  · rw [integral_withDensity_eq_integral_toReal_smul (continuous_coefficient ds a).enorm.measurable
      (ae_of_all _ fun _ => enorm_lt_top)]
    apply integral_congr_ae (ae_of_all _ fun u => ?_)
    change f (w * u.val * g) * complexWhittakerCharacter a u.val =
      ‖coefficient ds a u‖ₑ.toReal •
        ((unitPhase ds a u : ℂ) * f ((kpart (w * u.val)).val * g))
    rw [apply_mul_eq_borelScalar hf, toReal_enorm, Complex.real_smul]
    have hphase : (‖coefficient ds a u‖ : ℂ) * (unitPhase ds a u : ℂ) = coefficient ds a u := by
      change (‖coefficient ds a u‖ : ℂ) * (coefficient ds a u / (‖coefficient ds a u‖ : ℂ)) = _
      rw [mul_comm, div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr
        (norm_ne_zero_iff.mpr (coefficient_ne_zero ds a u)))]
    change _ = (‖coefficient ds a u‖ : ℂ) * ((unitPhase ds a u : ℂ) * f ((kpart (w * u.val)).val * g))
    rw [← mul_assoc, hphase, coefficient]
    ring
  · have hk : Continuous (fun p : Y => p.1.val * g) :=
      (continuous_subtype_val.comp continuous_fst).mul continuous_const
    exact ((continuous_subtype_val.comp continuous_snd).mul
      (hf.1.continuous.comp hk)).aestronglyMeasurable

private def leftAction (p : Y) : Mat →L[ℝ] Mat :=
  (ContinuousLinearMap.mul ℝ Mat) p.1.val.val

private theorem continuous_leftAction : Continuous (leftAction (r := r)) :=
  (ContinuousLinearMap.mul ℝ Mat).continuous.comp
    (Units.continuous_val.comp (continuous_subtype_val.comp continuous_fst))

private def compactExtension (μ : AdditiveHaarMeasure ℂ) (ds : List ComplexCharacterData)
    (a : ℂˣ) (f : G → ℂ) (x : Mat) : ℂ :=
  ∫ p : Y, (p.2 : ℂ) * unitsExtension f (leftAction p x) ∂compactMeasure μ ds a

private theorem compactExtension_agrees (μ : AdditiveHaarMeasure ℂ) (ds : List ComplexCharacterData)
    (a : ℂˣ) {f : G → ℂ} (hf : f ∈ complexStandardModule (r + 1) ds) (g : G) :
    openCellIntegral a (entryHaar μ (r + 1)) f g = compactExtension μ ds a f g.val := by
  rw [openCellIntegral_compact μ ds a hf]
  unfold compactExtension
  apply integral_congr_ae (ae_of_all _ fun p => ?_)
  have h : leftAction p g.val = (p.1.val * g).val := rfl
  rw [h, unitsExtension_val]

private theorem compactExtension_regularity (μ : AdditiveHaarMeasure ℂ) (ds : List ComplexCharacterData)
    (a : ℂˣ) (he : IsStrictlyDominant (complexPositionExponent ds) r)
    {f : G → ℂ} (hf : f ∈ complexStandardModule (r + 1) ds) :
    ContDiffOn ℝ ∞ (compactExtension μ ds a f) {x : Mat | IsUnit x} ∧
    ∀ x : Mat, IsUnit x →
      HasFDerivAt (compactExtension μ ds a f)
        (∫ p : Y, (p.2 : ℂ) • ((fderiv ℝ (unitsExtension f) (leftAction p x)).comp (leftAction p))
          ∂compactMeasure μ ds a) x := by
  have : IsFiniteMeasure (compactMeasure μ ds a) := compactMeasure_finite μ ds a he
  have h := Langlands.Analysis.compactLinearParameterIntegral Y Mat Mat (compactMeasure μ ds a)
    Set.univ isCompact_univ {x | IsUnit x} isOpen_setOf_isUnit_matrix
    {x | IsUnit x} isOpen_setOf_isUnit_matrix (fun p => (p.2 : ℂ))
    (continuous_subtype_val.comp continuous_snd) leftAction continuous_leftAction (unitsExtension f)
    (contDiffOn_unitsExtension hf.1) (fun p _ x hx => p.1.val.isUnit.mul hx)
  unfold compactExtension
  simpa only [Measure.restrict_univ, Set.mem_ofPred_eq] using h

/-- Smoothness of the absolutely convergent open-cell integral at all group arguments. -/
theorem contMDiff_openCellIntegral (μ : AdditiveHaarMeasure ℂ) (ds : List ComplexCharacterData)
    (a : ℂˣ) (he : IsStrictlyDominant (complexPositionExponent ds) r)
    {f : G → ℂ} (hf : f ∈ complexStandardModule (r + 1) ds) :
    ContMDiff (matrixModel ℂ (r + 1)) 𝓘(ℝ, ℂ) ∞ (openCellIntegral a (entryHaar μ (r + 1)) f) :=
  contMDiff_of_contDiffOn (compactExtension_regularity μ ds a he hf).1
    (compactExtension_agrees μ ds a hf)

/-- Right differentiation commutes with the open-cell integral on the strict chamber. -/
theorem rightDerivative_openCellIntegral (μ : AdditiveHaarMeasure ℂ) (ds : List ComplexCharacterData)
    (a : ℂˣ) (he : IsStrictlyDominant (complexPositionExponent ds) r)
    {f f' : G → ℂ} (hf : f ∈ complexStandardModule (r + 1) ds)
    (hf' : f' ∈ complexStandardModule (r + 1) ds) (X : Mat)
    (hderiv : f' = rightDerivative (matrixModel ℂ (r + 1)) X f) :
    rightDerivative (matrixModel ℂ (r + 1)) X (openCellIntegral a (entryHaar μ (r + 1)) f) =
      openCellIntegral a (entryHaar μ (r + 1)) f' := by
  have : IsFiniteMeasure (compactMeasure μ ds a) := compactMeasure_finite μ ds a he
  funext g
  let D : Y → Mat →L[ℝ] ℂ := fun p =>
    (p.2 : ℂ) • ((fderiv ℝ (unitsExtension f) (leftAction p g.val)).comp (leftAction p))
  have hD : HasFDerivAt (compactExtension μ ds a f) (∫ p, D p ∂compactMeasure μ ds a) g.val :=
    (compactExtension_regularity μ ds a he hf).2 _ g.isUnit
  have hext : unitsExtension (openCellIntegral a (entryHaar μ (r + 1)) f) =ᶠ[𝓝 g.val]
      compactExtension μ ds a f := by
    filter_upwards [isOpen_setOf_isUnit_matrix.mem_nhds g.isUnit] with x hx
    obtain ⟨h, rfl⟩ := hx
    rw [unitsExtension_val, compactExtension_agrees μ ds a hf]
  have hcontD : Continuous D := by
    have hF := Langlands.Analysis.CompactLinearParameterIntegral.continuousOn_partialDeriv
      (k := (Set.univ : Set Y)) (s := {x : Mat | IsUnit x})
      isOpen_setOf_isUnit_matrix (continuous_subtype_val.comp continuous_snd)
      continuous_leftAction (continuous_const (y := (0 : Mat))) (contDiffOn_unitsExtension hf.1)
      (fun p _ x hx => by rw [add_zero]; exact p.1.val.isUnit.mul hx)
    have h := hF.comp (s := Set.univ)
      (continuous_id.prodMk (continuous_const (y := g.val))).continuousOn
      (fun _ _ => ⟨Set.mem_univ _, g.isUnit⟩)
    simpa only [continuousOn_univ, add_zero, Function.comp_def, id_eq, D] using h
  rw [rightDerivative_eq_fderiv (contMDiff_openCellIntegral μ ds a he hf), hext.fderiv_eq,
    hD.fderiv, ContinuousLinearMap.integral_apply
      (hcontD.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace D)),
    openCellIntegral_compact μ ds a hf']
  apply integral_congr_ae (ae_of_all _ fun p => ?_)
  rw [hderiv, rightDerivative_eq_fderiv hf.1]
  unfold D
  have hy : leftAction p (g.val * X) = (p.1.val * g).val * X := by
    change p.1.val.val * (g.val * X) = (p.1.val.val * g.val) * X
    exact (Matrix.mul_assoc _ _ _).symm
  simp only [smul_apply, ContinuousLinearMap.comp_apply, hy, smul_eq_mul]
  rfl

variable (r) in
/-- The open-cell integral is smooth in the group variable and commutes with right
differentiation on the strict upper-Borel chamber. -/
def ComplexJacquetChamberSmoothStatement : Prop :=
  ∀ (μ : AdditiveHaarMeasure ℂ) (ds : List ComplexCharacterData) (a : ℂˣ),
    IsStrictlyDominant (complexPositionExponent ds) r →
    ∀ f ∈ complexStandardModule (r + 1) ds,
      ContMDiff (matrixModel ℂ (r + 1)) 𝓘(ℝ, ℂ) ∞ (openCellIntegral a (entryHaar μ (r + 1)) f) ∧
      ∀ (X : Mat) (f' : G → ℂ), f' ∈ complexStandardModule (r + 1) ds →
        f' = rightDerivative (matrixModel ℂ (r + 1)) X f →
        rightDerivative (matrixModel ℂ (r + 1)) X (openCellIntegral a (entryHaar μ (r + 1)) f) =
          openCellIntegral a (entryHaar μ (r + 1)) f'

theorem complexJacquetChamberSmooth : ComplexJacquetChamberSmoothStatement r := by
  intro μ ds a he f hf
  exact ⟨contMDiff_openCellIntegral μ ds a he hf,
    fun X _ hf' hderiv => rightDerivative_openCellIntegral μ ds a he hf hf' X hderiv⟩

end Langlands.Global.RankinSelbergGlobal.ComplexJacquetChamberSmooth
