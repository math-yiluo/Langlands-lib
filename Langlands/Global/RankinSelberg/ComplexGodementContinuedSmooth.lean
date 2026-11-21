import Langlands.Global.RankinSelberg.ComplexGodementParametric
import Langlands.Analysis.SchwartzMatrixNorm
import Langlands.Representation.Archimedean.ComplexPrincipalSeriesExtension
import Langlands.Representation.Archimedean.MatrixGroupDifferentiation
import Mathlib.LinearAlgebra.Matrix.Bilinear

/-! # Smoothness of the continued Godement values in the group argument -/

noncomputable section

open MeasureTheory Set
open scoped Classical ContDiff Manifold Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGodementContinuedSmooth

open Langlands.Archimedean Langlands.Archimedean.MatrixGroupDifferentiation
open Langlands.GeneralLinear (determinant)
open Langlands.HarmonicAnalysis (AdditiveHaarMeasure)
open Langlands.LocalFactor.Archimedean (ComplexCharacterData complexScaledCharacter)
open Langlands.Analysis.SchwartzMatrixNorm (EntrySchwartz)
open Langlands.Analysis.SchwartzPartialFourier (transformLinear_apply)
open ComplexGodement (characterWeight normPower)
open ComplexGodementAddedCharacter (continuedValue rightTest rightTest_apply)
open ComplexGodementColumnChange (iteratedKernel iteratedKernel_eq)
open ComplexGodementParametric (directionalTest directionalTest_apply continuous_continuedValue
  hasDerivAt_integral_iteratedKernel_curve)
open ComplexGodementPartialFourier (partialSchwartz partialSchwartz_apply)
open ComplexGodementTranslatedBounds (complexGodementTranslatedBounds)
open ComplexGodementWhittaker (kernelBase)
open ComplexGodementWhittakerFamily (HasUniformSimpleRootBound)
open ArchimedeanLocal (complexNormalizedAbs)

attribute [local instance] ArchimedeanLocal.archimedeanComplexGLMeasurable
  ArchimedeanLocal.archimedeanComplexGLBorel

variable {r : ℕ}
local notation "G" => Langlands.GeneralLinear (r + 1) ℂ
local notation "G'" => Langlands.GeneralLinear (r + 1 + 1) ℂ
local notation "Square" => Matrix (Fin (r + 1 + 1)) (Fin (r + 1 + 1)) ℂ
local notation "Rect" => Matrix (Fin (r + 1)) (Fin (r + 1 + 1)) ℂ
local notation "Test" => EntrySchwartz (r + 1) (r + 1 + 1)

private def prefactor (d : ComplexCharacterData) (s : ℂ) (g : G') : ℂ :=
  (d.character ((-1 : ℂˣ) ^ (r + 1)) : ℂ) * characterWeight d (((r + 1 : ℕ) : ℂ) / 2 + s) (determinant g)

private theorem normPower_detPower (g : G') (s : ℂ) :
    normPower s (determinant g) = ArchimedeanLocal.detPower complexNormalizedAbs g s := by
  change ((complexNormalizedAbs g.val.det : ℝ) : ℂ) ^ s = _
  have hp : 0 < complexNormalizedAbs g.val.det := pow_pos (norm_pos_iff.mpr g.det_ne_zero) _
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hp.ne'), ← Complex.ofReal_log hp.le]
  simp only [ArchimedeanLocal.detPower, mul_comm _ s]

private theorem prefactor_eq (d : ComplexCharacterData) (s : ℂ) (g : G') :
    prefactor d s g =
      ((d.character ((-1 : ℂˣ) ^ (r + 1)) : ℂ) *
        characterWeight d (((r + 1 : ℕ) : ℂ) / 2) (determinant g)) *
        ArchimedeanLocal.detPower complexNormalizedAbs g s := by
  rw [← normPower_detPower]
  change _ * ((d.character (determinant g) : ℂ) *
    ((complexNormalizedAbs g.val.det : ℝ) : ℂ) ^ ((((r + 1 : ℕ) : ℂ) / 2) + s)) = _
  have hz : ((complexNormalizedAbs g.val.det : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 (norm_ne_zero_iff.mpr g.det_ne_zero))
  rw [Complex.cpow_add _ _ hz]
  simp only [characterWeight, normPower, MonoidHom.coe_mk, OneHom.coe_mk, mul_assoc]
  rfl

private theorem prefactor_ne_zero (d : ComplexCharacterData) (s : ℂ) (g : G') :
    prefactor d s g ≠ 0 := by
  exact mul_ne_zero (Units.ne_zero _)
    (((Group.isUnit (determinant g)).map (characterWeight d _)).ne_zero)

private theorem contDiffAt_integerPower (k : ℤ) {z : ℂ} (hz : z ≠ 0) :
    ContDiffAt ℝ ∞ (fun w : ℂ => w ^ k) z := by
  have h : ContDiffAt ℝ ∞ (fun w : ℂ => w) z := contDiffAt_id
  cases k with
  | ofNat k => simpa only [Int.ofNat_eq_natCast, zpow_natCast] using h.pow k
  | negSucc k =>
      rw [show (fun w : ℂ => w ^ Int.negSucc k) = (fun w : ℂ => w ^ (k + 1))⁻¹ by
        funext w
        exact zpow_negSucc w k]
      exact (h.pow (k + 1)).inv (pow_ne_zero _ hz)

private def characterWeightFunction (d : ComplexCharacterData) (s : ℂ) (z : ℂ) : ℂ :=
  ((z / (‖z‖ : ℂ)) ^ d.weight * (‖z‖ : ℂ) ^ (2 * d.exponent)) *
    ((‖z‖ ^ 2 : ℝ) : ℂ) ^ s

private theorem contDiffOn_characterWeightFunction (d : ComplexCharacterData) (s : ℂ) :
    ContDiffOn ℝ ∞ (characterWeightFunction d s) {z : ℂ | z ≠ 0} := by
  intro z hz
  have hz' : z ≠ 0 := hz
  have hpos : 0 < ‖z‖ := norm_pos_iff.mpr hz'
  have hn : ContDiffAt ℝ ∞ (fun w : ℂ => ‖w‖) z := contDiffAt_norm ℝ hz'
  have hnc : ContDiffAt ℝ ∞ (fun w : ℂ => (‖w‖ : ℂ)) z :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp z hn
  have hunit : ContDiffAt ℝ ∞ (fun w : ℂ => w / (‖w‖ : ℂ)) z := by
    simp only [div_eq_mul_inv]
    exact contDiffAt_id.mul (hnc.inv (by exact_mod_cast hpos.ne'))
  have hunit_ne : z / (‖z‖ : ℂ) ≠ 0 := div_ne_zero hz' (by exact_mod_cast hpos.ne')
  exact (((contDiffAt_integerPower d.weight hunit_ne).comp z hunit).mul
    (ComplexPrincipalSeriesExtension.contDiffAt_ofReal_cpow hn hpos (2 * d.exponent))).mul
      (ComplexPrincipalSeriesExtension.contDiffAt_ofReal_cpow (hn.pow 2) (pow_pos hpos 2) s)
      |>.contDiffWithinAt

private theorem contMDiff_characterWeight_det {n : ℕ} (d : ComplexCharacterData) (s : ℂ) :
    ContMDiff (matrixModel ℂ n) 𝓘(ℝ, ℂ) ∞
      (fun g : Langlands.GeneralLinear n ℂ => characterWeight d s (determinant g)) := by
  have hdet : ContDiff ℝ ∞ (fun X : Matrix (Fin n) (Fin n) ℂ => X.det) :=
    ComplexMaximalParabolicIntegration.contDiff_det
  have hA : ContDiffOn ℝ ∞ (fun X : Matrix (Fin n) (Fin n) ℂ => characterWeightFunction d s X.det)
      {X | IsUnit X} :=
    (contDiffOn_characterWeightFunction d s).comp hdet.contDiffOn fun X hX =>
      ((Matrix.isUnit_iff_isUnit_det X).mp hX).ne_zero
  refine contMDiff_of_contDiffOn hA fun g => ?_
  change (d.character (determinant g) : ℂ) * normPower s (determinant g) =
    characterWeightFunction d s g.val.det
  rw [d.character_eq]
  rfl

private theorem contMDiff_prefactor (d : ComplexCharacterData) (s : ℂ) :
    ContMDiff (matrixModel ℂ (r + 1 + 1)) 𝓘(ℝ, ℂ) ∞ (prefactor (r := r) d s) :=
  (contDiff_mul (𝕜 := ℝ) (𝔸 := ℂ)).contMDiff.comp
    (contMDiff_const.prodMk_space (contMDiff_characterWeight_det d _))

/-- The outer integral with the test translated on the right. -/
def translatedIntegral (ν : Measure G) (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ)
    (d : ComplexCharacterData) (W : G → ℂ) (s : ℂ) (Φ : Test) (g : G') : ℂ :=
  ∫ h, iteratedKernel (complexScaledCharacter a) μ d (rightTest g Φ) W s h ∂ν

open scoped Matrix.Norms.Elementwise in
private def rightField (X : Square) : Rect →L[ℝ] Rect :=
  (mulRightLinearMap (Fin (r + 1)) ℝ X).toContinuousLinearMap

@[simp]
private theorem rightField_apply (X : Square) (Y : Rect) : rightField X Y = Y * X := rfl

open scoped Matrix.Norms.Elementwise in
/-- The real linear family of right-invariant differential operators on the test. -/
def testDerivative (Φ : Test) : Square →ₗ[ℝ] Test where
  toFun X := directionalTest (rightField X) Φ
  map_add' X Y := by
    apply SchwartzMap.ext
    intro Z
    simp only [directionalTest_apply, rightField_apply, Matrix.mul_add, map_add, add_apply]
  map_smul' c X := by
    apply SchwartzMap.ext
    intro Z
    simp only [directionalTest_apply, rightField_apply, Matrix.mul_smul, map_smul, RingHom.id_apply,
      smul_apply]

private theorem partialSchwartz_add (a : ℂˣ) (μ : AdditiveHaarMeasure ℂ) (Φ Ψ : Test) :
    partialSchwartz a μ (Φ + Ψ) = partialSchwartz a μ Φ + partialSchwartz a μ Ψ := by
  simp only [partialSchwartz, ← transformLinear_apply, map_add, smul_add]

private theorem partialSchwartz_smul (a : ℂˣ) (μ : AdditiveHaarMeasure ℂ) (c : ℂ) (Φ : Test) :
    partialSchwartz a μ (c • Φ) = c • partialSchwartz a μ Φ := by
  simp only [partialSchwartz, ← transformLinear_apply, map_smul]
  rw [smul_comm]

open scoped Matrix.Norms.Elementwise in
private def translatedKernelLinear (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ) (d : ComplexCharacterData)
    (W : G → ℂ) (s : ℂ) (g : G') (h : G) : Test →ₗ[ℂ] ℂ where
  toFun Φ := iteratedKernel (complexScaledCharacter a) μ d (rightTest g Φ) W s h
  map_add' Φ Ψ := by
    have he (f : Test) := iteratedKernel_eq (complexScaledCharacter a) μ d (rightTest g f)
      (partialSchwartz a μ (rightTest g f)) (partialSchwartz_apply a μ (rightTest g f)) W s h
    have hr : rightTest g (Φ + Ψ) = rightTest g Φ + rightTest g Ψ := SchwartzMap.ext fun _ => rfl
    rw [he (Φ + Ψ), hr]
    simp only [he, partialSchwartz_add, kernelBase, add_apply, add_mul]
  map_smul' c Φ := by
    have he (f : Test) := iteratedKernel_eq (complexScaledCharacter a) μ d (rightTest g f)
      (partialSchwartz a μ (rightTest g f)) (partialSchwartz_apply a μ (rightTest g f)) W s h
    have hr : rightTest g (c • Φ) = c • rightTest g Φ := SchwartzMap.ext fun _ => rfl
    rw [he (c • Φ), hr]
    simp only [he, partialSchwartz_smul, kernelBase, smul_apply, smul_eq_mul,
      RingHom.id_apply, mul_assoc]

section Estimates

variable {P : Type} (ν : Measure (Langlands.GeneralLinear (r + 1) ℂ)) [ν.IsHaarMeasure]
  (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ) (d : ComplexCharacterData)
  {S : Set P} (W : P → Langlands.GeneralLinear (r + 1) ℂ → ℂ)
  (hWc : ∀ p ∈ S, Continuous (W p)) (hWb : HasUniformSimpleRootBound S W)
  {p : P} (hp : p ∈ S) (s : ℂ)

include hWc hWb hp in
private theorem continuous_translatedIntegral (Φ : Test) :
    Continuous (translatedIntegral ν μ a d (W p) s Φ) := by
  let t := s - (((r + 1 : ℕ) + 1 : ℂ) / 2)
  have ht : (((r + 1 : ℕ) + 1 : ℂ) / 2) + t = s := by dsimp [t]; ring
  have hc := continuous_continuedValue ν μ a d S W hWc hWb p hp Φ t
  have hdiv := hc.div (contMDiff_prefactor (r := r) d t).continuous (prefactor_ne_zero d t)
  refine hdiv.congr ?_
  intro g
  change continuedValue ν μ d a Φ (W p) g t / prefactor d t g =
    translatedIntegral ν μ a d (W p) s Φ g
  rw [continuedValue, ht, ← prefactor_eq]
  exact mul_div_cancel_left₀ _ (prefactor_ne_zero d t g)

private def translatedIntegralLinear (g : G')
    (hInt : ∀ Φ : Test, Integrable (fun h => translatedKernelLinear μ a d (W p) s g h Φ) ν) :
    Test →ₗ[ℂ] ℂ where
  toFun Φ := translatedIntegral ν μ a d (W p) s Φ g
  map_add' Φ Ψ := by
    change (∫ h, translatedKernelLinear μ a d (W p) s g h (Φ + Ψ) ∂ν) = _
    simp only [map_add]
    exact integral_add (hInt Φ) (hInt Ψ)
  map_smul' c Φ := by
    change (∫ h, translatedKernelLinear μ a d (W p) s g h (c • Φ) ∂ν) = _
    simp only [map_smul, RingHom.id_apply, integral_smul]
    rfl

private noncomputable def matrixBasis := Module.finBasis ℝ Square
local notation "BasisIndex" => Fin (Module.finrank ℝ Square)

private def coordinate (i : BasisIndex) : Square →L[ℝ] ℝ :=
  ((matrixBasis (r := r)).coord i).toContinuousLinearMap

private def derivativeField (Φ : Test) (g : G') : Square →L[ℝ] ℂ :=
  ∑ i, (coordinate i).smulRight (translatedIntegral ν μ a d (W p) s (testDerivative Φ (matrixBasis i)) g)

include hWc hWb hp in
private theorem continuous_derivativeField (Φ : Test) :
    Continuous (derivativeField ν μ a d W (p := p) s Φ) := by
  apply continuous_finsetSum
  intro i _
  exact ((ContinuousLinearMap.smulRightL ℝ Square ℂ) (coordinate i)).continuous.comp
    (continuous_translatedIntegral ν μ a d W hWc hWb hp s _)

include hWc hWb hp in
private theorem derivativeField_apply (Φ : Test) (g : G') (X : Square) :
    derivativeField ν μ a d W (p := p) s Φ g X =
      translatedIntegral ν μ a d (W p) s (testDerivative Φ X) g := by
  obtain ⟨I, N, B, _, _, hb⟩ := complexGodementTranslatedBounds ν μ a d S W hWc hWb
    |(s - 1).re| (abs_nonneg _)
  let L := ((translatedIntegralLinear ν μ a d W (p := p) s g
    (fun f => (hb p hp s le_rfl g f).1)).restrictScalars ℝ).comp
    (testDerivative Φ)
  have he := congrArg L ((matrixBasis (r := r)).sum_repr X)
  simp only [map_sum, map_smul] at he
  change _ = L X
  rw [← he]
  simp only [derivativeField, sum_apply, ContinuousLinearMap.smulRight_apply,
    coordinate, L, LinearMap.comp_apply, LinearMap.restrictScalars_apply, translatedIntegralLinear]
  exact Finset.sum_congr rfl fun _ _ => rfl

open scoped Matrix.Norms.Elementwise in
set_option maxHeartbeats 750000 in
private theorem hasDerivAt_rectangular_exponential (g : G') (X : Square) (t : ℝ) (Y : Rect) :
    HasDerivAt (fun u : ℝ => Y * (g * matrixExponentialGL ℂ (r + 1 + 1) (u • X)).val)
      (rightField X (Y * (g * matrixExponentialGL ℂ (r + 1 + 1) (t • X)).val)) t := by
  let : SeminormedAddCommGroup Square := Matrix.linftyOpSeminormedAddCommGroup
  let : NormedAddCommGroup Square := Matrix.linftyOpNormedAddCommGroup
  let : NormedSpace ℝ Square := Matrix.linftyOpNormedSpace
  let L : Square →L[ℝ] Rect := (mulLeftLinearMap (Fin (r + 1 + 1)) ℝ (Y * g.val)).toContinuousLinearMap
  have h := L.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_exp_smul_const (𝕂 := ℝ) X t)
  change HasDerivAt (fun u : ℝ => (Y * g.val) * NormedSpace.exp (u • X))
    ((Y * g.val) * (NormedSpace.exp (t • X) * X)) t at h
  simpa only [Units.val_mul, matrixExponentialGL_coe, rightField_apply, Matrix.mul_assoc] using h

include hWc hWb hp in
private theorem hasFDerivAt_translatedIntegral (Φ : Test) (g : G') :
    HasFDerivAt (unitsExtension (translatedIntegral ν μ a d (W p) s Φ))
      ((derivativeField ν μ a d W (p := p) s Φ g).comp (leftMul g).symm.toContinuousLinearMap) g.val := by
  apply hasFDerivAt_unitsExtension (continuous_derivativeField ν μ a d W hWc hWb hp s Φ) _ g
  intro k X t
  let γ (u : ℝ) := k * matrixExponentialGL ℂ (r + 1 + 1) (u • X)
  have hc : Continuous γ := continuous_const.mul
    (continuous_matrixExponentialGL.comp (continuous_id.smul continuous_const))
  rw [derivativeField_apply ν μ a d W hWc hWb hp s]
  exact hasDerivAt_integral_iteratedKernel_curve ν μ a d S W hWc hWb p hp Φ s γ hc (rightField X)
    (fun t Y => hasDerivAt_rectangular_exponential k X t Y) t

private def inverseCoordinate (i : BasisIndex) (X : Square) : Square →L[ℝ] ℝ :=
  (coordinate i).comp (ContinuousLinearMap.mul ℝ Square (Ring.inverse X))

private theorem contDiffOn_inverseCoordinate (i : BasisIndex) (m : ℕ) :
    ContDiffOn ℝ m (inverseCoordinate i) {X : Square | IsUnit X} := by
  have hInv : ContDiffOn ℝ m (Ring.inverse : Square → Square) {X | IsUnit X} := by
    rintro _ ⟨g, rfl⟩
    exact (contDiffAt_ringInverse ℝ g).contDiffWithinAt
  exact ((ContinuousLinearMap.compL ℝ Square Square ℝ (coordinate i)).contDiff.comp_contDiffOn
    ((ContinuousLinearMap.mul ℝ Square).contDiff.comp_contDiffOn hInv))

include ν μ a d hWc hWb hp s in
/-- A translated Godement integral is smooth in the larger group argument. -/
theorem contMDiff_translatedIntegral (Φ : Test) :
    ContMDiff (matrixModel ℂ (r + 1 + 1)) 𝓘(ℝ, ℂ) ∞ (translatedIntegral ν μ a d (W p) s Φ) := by
  let U : Set Square := {X | IsUnit X}
  have hU : IsOpen U := isOpen_setOf_isUnit_matrix
  apply contMDiff_of_contDiffOn (ψ := unitsExtension (translatedIntegral ν μ a d (W p) s Φ)) _
    (fun g => (unitsExtension_val _ g).symm)
  suffices h : ∀ (m : ℕ) (Ψ : Test), ContDiffOn ℝ m (unitsExtension (translatedIntegral ν μ a d (W p) s Ψ)) U by
    exact contDiffOn_infty.mpr fun m => h m Φ
  intro m
  induction m with
  | zero =>
      intro Ψ
      rw [Nat.cast_zero, contDiffOn_zero]
      rintro _ ⟨g, rfl⟩
      exact (hasFDerivAt_translatedIntegral ν μ a d W hWc hWb hp s Ψ g).continuousAt.continuousWithinAt
  | succ m ih =>
      intro Ψ
      rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen hU]
      refine ⟨?_, by simp, ?_⟩
      · rintro _ ⟨g, rfl⟩
        exact (hasFDerivAt_translatedIntegral ν μ a d W hWc hWb hp s Ψ g).differentiableAt.differentiableWithinAt
      · let F (i : BasisIndex) := unitsExtension (translatedIntegral ν μ a d (W p) s
            (testDerivative Ψ (matrixBasis i)))
        let D (X : Square) := ∑ i, (inverseCoordinate i X).smulRight (F i X)
        have hD : ContDiffOn ℝ m D U := by
          apply ContDiffOn.sum
          intro i _
          exact ((ContinuousLinearMap.smulRightL ℝ Square ℂ).contDiff.comp_contDiffOn
            (contDiffOn_inverseCoordinate i m)).clm_apply (ih _)
        refine hD.congr ?_
        rintro _ ⟨g, rfl⟩
        rw [(hasFDerivAt_translatedIntegral ν μ a d W hWc hWb hp s Ψ g).fderiv]
        ext X
        simp only [D, F, inverseCoordinate, Ring.inverse_unit, ContinuousLinearMap.comp_apply,
          derivativeField, sum_apply, ContinuousLinearMap.smulRight_apply,
          ContinuousLinearEquiv.coe_coe, leftMul_symm_apply, unitsExtension_val]
        exact Finset.sum_congr rfl fun _ _ => rfl

include ν μ a d hWc hWb hp s in
/-- The continued Godement value is smooth in the larger group at every fixed parameter. -/
theorem contMDiff_continuedValue (Φ : Test) :
    ContMDiff (matrixModel ℂ (r + 1 + 1)) 𝓘(ℝ, ℂ) ∞ (fun g => continuedValue ν μ d a Φ (W p) g s) := by
  have he : (fun g => continuedValue ν μ d a Φ (W p) g s) = fun g => prefactor d s g *
      translatedIntegral ν μ a d (W p) ((((r + 1 : ℕ) + 1 : ℂ) / 2) + s) Φ g := by
    funext g
    rw [continuedValue, prefactor_eq]
    rfl
  rw [he]
  exact (contDiff_mul (𝕜 := ℝ) (𝔸 := ℂ)).contMDiff.comp
    ((contMDiff_prefactor d s).prodMk_space (contMDiff_translatedIntegral ν μ a d W hWc hWb hp _ Φ))

end Estimates

variable (r) in
/-- Under the uniform smaller-rank estimate, the exact continuation is smooth on the group. -/
def ComplexGodementContinuedSmoothStatement : Prop :=
  ∀ {P : Type} (ν : Measure G) [ν.IsHaarMeasure] (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ)
    (d : ComplexCharacterData) (S : Set P) (W : P → G → ℂ),
    (∀ p ∈ S, Continuous (W p)) → HasUniformSimpleRootBound S W →
    ∀ p ∈ S, ∀ (Φ : Test) (s : ℂ),
      ContMDiff (matrixModel ℂ (r + 1 + 1)) 𝓘(ℝ, ℂ) ∞ (fun g => continuedValue ν μ d a Φ (W p) g s)

theorem complexGodementContinuedSmooth : ComplexGodementContinuedSmoothStatement r := by
  intro P ν hν μ a d S W hWc hWb p hp Φ s
  exact contMDiff_continuedValue ν μ a d W hWc hWb hp s Φ

end Langlands.Global.RankinSelbergGlobal.ComplexGodementContinuedSmooth
