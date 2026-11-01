import Langlands.Representation.RankinSelberg.AdjacentRankCompactMatrixConvergence
import Langlands.HarmonicAnalysis.SchwartzBruhatProduct
import Langlands.HarmonicAnalysis.PadicRectangularHaarScalingProof

noncomputable section

open MeasureTheory Matrix
open scoped BigOperators NNReal ENNReal

namespace Langlands.RankinSelberg.AdjacentDoubleIntegral

open HarmonicAnalysis Whittaker GeneralLinear AdjacentCompactMatrix

universe uF uV
variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance doubleIntegralTopology : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance doubleIntegralValuativeRel : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance doubleIntegralLocalField : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance doubleIntegralT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance doubleIntegralNonarchRing : NonarchimedeanRing F.Carrier := by
  convert! ValuativeRel.nonarchimedeanRing F.Carrier
  exact Valuation.toTopologicalSpace_eq _
local instance doubleIntegralSecondCountable : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance doubleIntegralSigmaCompact : SigmaCompactSpace F.Carrier := F.canonicalTopologicalData.sigmaCompactSpace
local instance doubleIntegralMeasurable : MeasurableSpace F.Carrier := borel _
local instance doubleIntegralBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance doubleIntegralGLMeasurable (n : ℕ) : MeasurableSpace (GeneralLinear (n + 1) F.Carrier) := borel _
local instance doubleIntegralGLBorel (n : ℕ) : BorelSpace (GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
local instance doubleIntegralGLLocallyCompact (n : ℕ) : LocallyCompactSpace (GeneralLinear (n + 1) F.Carrier) :=
  F.canonicalTopologicalData.generalLinearLocallyCompactSpace (n + 1)
local instance doubleIntegralGLSecondCountable (n : ℕ) : SecondCountableTopology (GeneralLinear (n + 1) F.Carrier) :=
  F.canonicalTopologicalData.generalLinearSecondCountableTopology (n + 1)

local notation "abv" => normalizedAbsoluteValue F.canonicalTopologicalData


/-- The literal JPSS double-integral scalar kernel, after absorbing a fixed
ambient group element into the rectangular test. -/
def integrand (ψ : UnitaryAdditiveCharacter F.Carrier) {r : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (ℓ : glFunctionals ψ r σ) (χ : Quasicharacter F.Carrier)
    (Φ : SchwartzBruhat (Matrix (Fin (r + 1)) (Fin (r + 2)) F.Carrier))
    (W : (glCoefficientModel ψ r σ ℓ).toSubmodule)
    (x : Fin (r + 1) → F.Carrier) (h : GeneralLinear (r + 1) F.Carrier) : ℂ :=
  Φ (rectangularJoin h.val (h.val *ᵥ x)) * glModelFunction ψ r σ ℓ W h⁻¹ *
    (χ (determinant h) : ℂ) * determinantWeight abv h (((r + 2 : ℕ) : ℂ) / 2) *
      ψ.complex (-x (Fin.last r))

/-- Multiplication by an invertible matrix on column space. -/
def columnHomeomorph {n : ℕ} (h : GeneralLinear n F.Carrier) :
    (Fin n → F.Carrier) ≃ₜ (Fin n → F.Carrier) where
  toFun x := h.val *ᵥ x
  invFun x := (h⁻¹).val *ᵥ x
  left_inv x := by
    dsimp only
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec]
  right_inv x := by
    dsimp only
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec]
  continuous_toFun := continuous_const.matrix_mulVec continuous_id
  continuous_invFun := continuous_const.matrix_mulVec continuous_id

@[simp] theorem columnHomeomorph_apply {n : ℕ} (h : GeneralLinear n F.Carrier)
    (x : Fin n → F.Carrier) : columnHomeomorph F h x = h.val *ᵥ x := rfl

/-- The supplied row Haar scales by the reciprocal normalized determinant
under multiplication by the matrix on columns. -/
theorem rowMeasure_map_mulVec (ν : AdditiveHaarMeasure F.Carrier) {n : ℕ}
    (h : GeneralLinear n F.Carrier) :
    (rowMeasure ν n).map (fun x => h.val *ᵥ x) =
      (F.canonicalTopologicalData.normalizedAbsHom h.val.det)⁻¹ • rowMeasure ν n := by
  exact productMeasure_map_matrix ν.measure F.canonicalTopologicalData.normalizedAbsHom
    (fun a ha => padicScalarHaarScaling F F.canonicalTopologicalData ν.measure
      (Units.mk0 a ha)) h.det_ne_zero

/-- Integrability is preserved by this column substitution. -/
theorem integrable_comp_mulVec (ν : AdditiveHaarMeasure F.Carrier) {n : ℕ}
    (h : GeneralLinear n F.Carrier) {E : Type*} [NormedAddCommGroup E]
    (f : (Fin n → F.Carrier) → E) (hf : Integrable f (rowMeasure ν n)) :
    Integrable (fun x => f (h.val *ᵥ x)) (rowMeasure ν n) := by
  have hi := hf.smul_measure_nnreal
    (c := (F.canonicalTopologicalData.normalizedAbsHom h.val.det)⁻¹)
  rw [← rowMeasure_map_mulVec F ν h] at hi
  exact (columnHomeomorph F h).measurableEmbedding.integrable_map_iff.mp hi

/-- Exact Bochner change of variables, retaining the supplied Haar normalization. -/
theorem integral_mulVec (ν : AdditiveHaarMeasure F.Carrier) {n : ℕ}
    (h : GeneralLinear n F.Carrier) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : (Fin n → F.Carrier) → E) :
    (∫ x, f (h.val *ᵥ x) ∂rowMeasure ν n) =
      (F.canonicalTopologicalData.normalizedAbs h.val.det)⁻¹ •
        ∫ y, f y ∂rowMeasure ν n := by
  change (∫ x, f (columnHomeomorph F h x) ∂rowMeasure ν n) = _
  rw [← (columnHomeomorph F h).measurableEmbedding.integral_map f]
  change (∫ y, f y ∂(rowMeasure ν n).map (fun x => h.val *ᵥ x)) = _
  rw [rowMeasure_map_mulVec F ν h, integral_smul_nnreal_measure]
  simp only [NNReal.smul_def, NNReal.coe_inv,
    PadicField.TopologicalData.normalizedAbsHom_coe]

/-- The complex-valued norm of a Schwartz--Bruhat function. -/
def normTest {X : Type*} [TopologicalSpace X] (f : SchwartzBruhat X) : SchwartzBruhat X :=
  ⟨fun z => (‖f z‖ : ℂ), f.locallyConstant.comp (fun z : ℂ => (‖z‖ : ℂ)),
    f.hasCompactSupport.comp_left (g := fun z : ℂ => (‖z‖ : ℂ))
      (by simp only [norm_zero, Complex.ofReal_zero])⟩

/-- The integral of the absolute value of a last-column slice, as an actual
complex square-matrix Schwartz--Bruhat function. -/
def fiberNorm (ν : AdditiveHaarMeasure F.Carrier) (r : ℕ)
    (Φ : SchwartzBruhat (Matrix (Fin (r + 1)) (Fin (r + 2)) F.Carrier)) :
    SchwartzBruhat (Matrix (Fin (r + 1)) (Fin (r + 1)) F.Carrier) := by
  let f : SchwartzBruhat
      (Matrix (Fin (r + 1)) (Fin (r + 1)) F.Carrier × (Fin (r + 1) → F.Carrier)) :=
    Hecke.TestFunction.pullback
    (rectangularSplit (K := F.Carrier) (n := r + 1)).symm Φ
  exact SchwartzBruhat.partialIntegral (normTest f) (rowMeasure ν (r + 1))

theorem fiberNorm_apply (ν : AdditiveHaarMeasure F.Carrier) (r : ℕ)
    (Φ : SchwartzBruhat (Matrix (Fin (r + 1)) (Fin (r + 2)) F.Carrier))
    (A : Matrix (Fin (r + 1)) (Fin (r + 1)) F.Carrier) :
    fiberNorm F ν r Φ A = (∫ y, ‖Φ (rectangularJoin A y)‖ ∂rowMeasure ν (r + 1) : ℝ) := by
  change (∫ y, (‖Φ (rectangularJoin A y)‖ : ℂ) ∂rowMeasure ν (r + 1)) = _
  exact integral_complex_ofReal

/-- The slice-norm value is a nonnegative real number. -/
theorem norm_fiberNorm_apply (ν : AdditiveHaarMeasure F.Carrier) (r : ℕ)
    (Φ : SchwartzBruhat (Matrix (Fin (r + 1)) (Fin (r + 2)) F.Carrier))
    (A : Matrix (Fin (r + 1)) (Fin (r + 1)) F.Carrier) :
    ‖fiberNorm F ν r Φ A‖ = ∫ y, ‖Φ (rectangularJoin A y)‖ ∂rowMeasure ν (r + 1) := by
  rw [fiberNorm_apply, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]

/-- The column Jacobian reduces the exact half-modulus by one. -/
theorem jacobian_detWeight {r : ℕ} (h : GeneralLinear (r + 1) F.Carrier) :
    ((F.canonicalTopologicalData.normalizedAbs h.val.det)⁻¹ : ℂ) *
        determinantWeight abv h (((r + 2 : ℕ) : ℂ) / 2) =
      determinantWeight abv h ((r : ℂ) / 2) := by
  have he : ((r + 2 : ℕ) : ℂ) / 2 = (r : ℂ) / 2 + 1 := by push_cast; ring
  have hw : determinantWeight abv h 1 =
      (F.canonicalTopologicalData.normalizedAbs h.val.det : ℂ) := by
    simp only [determinantWeight, Complex.cpow_one, normalizedAbsoluteValue_apply]
  have hd : (F.canonicalTopologicalData.normalizedAbs h.val.det : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (F.canonicalTopologicalData.normalizedAbs_pos h.det_ne_zero)
  rw [he, determinantWeight_add_exponents, hw]
  field_simp

/-- Continuity of the literal two-variable kernel requires only smoothness. -/
theorem continuous_integrand (ψ : UnitaryAdditiveCharacter F.Carrier) {r : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (hσ : IsSmooth σ) (ℓ : glFunctionals ψ r σ)
    (χ : Quasicharacter F.Carrier)
    (Φ : SchwartzBruhat (Matrix (Fin (r + 1)) (Fin (r + 2)) F.Carrier))
    (W : (glCoefficientModel ψ r σ ℓ).toSubmodule) :
    Continuous (fun z : (Fin (r + 1) → F.Carrier) × GeneralLinear (r + 1) F.Carrier =>
      integrand F ψ σ ℓ χ Φ W z.1 z.2) := by
  have hc : Continuous (fun z : (Fin (r + 1) → F.Carrier) × GeneralLinear (r + 1) F.Carrier =>
      z.2.val) := Units.continuous_val.comp continuous_snd
  exact ((((Φ.continuous.comp (continuous_rectangularJoin.comp
      (hc.prodMk (hc.matrix_mulVec continuous_fst)))).mul
      ((glModelFunction_continuous ψ r σ hσ ℓ W).comp continuous_snd.inv)).mul
      (Units.continuous_val.comp (χ.continuous.comp
        ((F.canonicalTopologicalData.generalLinearDeterminant (r + 1)).continuous.comp
          continuous_snd)))).mul
      ((continuous_adjacentRank_determinantWeight F _ _).comp continuous_snd)).mul
      (ψ.continuous_complex.comp ((continuous_apply (Fin.last r)).comp continuous_fst).neg)

/-- Every fixed-matrix column section is integrable, without a twist restriction. -/
theorem integrable_column (ν : AdditiveHaarMeasure F.Carrier)
    (ψ : UnitaryAdditiveCharacter F.Carrier) {r : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (ℓ : glFunctionals ψ r σ) (χ : Quasicharacter F.Carrier)
    (Φ : SchwartzBruhat (Matrix (Fin (r + 1)) (Fin (r + 2)) F.Carrier))
    (W : (glCoefficientModel ψ r σ ℓ).toSubmodule)
    (h : GeneralLinear (r + 1) F.Carrier) :
    Integrable (integrand F ψ σ ℓ χ Φ W · h) (rowMeasure ν (r + 1)) := by
  let f := Hecke.TestFunction.pullback (columnHomeomorph F h) (rectangularSlice Φ h.val)
  have hc : Continuous (integrand F ψ σ ℓ χ Φ W · h) :=
    ((((f.continuous.mul continuous_const).mul continuous_const).mul
    continuous_const).mul (ψ.continuous_complex.comp (continuous_apply (Fin.last r)).neg))
  exact hc.integrable_of_hasCompactSupport
    (((f.hasCompactSupport.mul_right).mul_right).mul_right).mul_right

/-- Exact reduction of the integrated column norm to the square-matrix norm. -/
theorem integral_norm_column (ν : AdditiveHaarMeasure F.Carrier)
    (ψ : UnitaryAdditiveCharacter F.Carrier) {r : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (ℓ : glFunctionals ψ r σ) (χ : Quasicharacter F.Carrier)
    (Φ : SchwartzBruhat (Matrix (Fin (r + 1)) (Fin (r + 2)) F.Carrier))
    (W : (glCoefficientModel ψ r σ ℓ).toSubmodule)
    (h : GeneralLinear (r + 1) F.Carrier) :
    (∫ x, ‖integrand F ψ σ ℓ χ Φ W x h‖ ∂rowMeasure ν (r + 1)) =
      ‖fiberNorm F ν r Φ h.val * glModelFunction ψ r σ ℓ W h⁻¹ *
        (χ (determinant h) : ℂ) * determinantWeight abv h ((r : ℂ) / 2)‖ := by
  simp only [integrand, norm_mul, UnitaryAdditiveCharacter.norm_complex, mul_one]
  rw [integral_mul_const, integral_mul_const, integral_mul_const,
    integral_mulVec F ν h (fun y => ‖Φ (rectangularJoin h.val y)‖)]
  rw [norm_fiberNorm_apply]
  have hj := congrArg norm (jacobian_detWeight F h)
  simp only [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (F.canonicalTopologicalData.normalizedAbs_nonneg _)] at hj
  simp only [smul_eq_mul]
  rw [← hj]
  ring

/-- Column integration is exactly inverse-character partial Fourier evaluation
at the actual adjacent-rank kernel matrix. -/
theorem integral_column_partialFourier (ν : AdditiveHaarMeasure F.Carrier)
    (ψ : UnitaryAdditiveCharacter F.Carrier) {r : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (ℓ : glFunctionals ψ r σ) (χ : Quasicharacter F.Carrier)
    (Φ : SchwartzBruhat (Matrix (Fin (r + 1)) (Fin (r + 2)) F.Carrier))
    (W : (glCoefficientModel ψ r σ ℓ).toSubmodule)
    (h : GeneralLinear (r + 1) F.Carrier) :
    (∫ x, integrand F ψ σ ℓ χ Φ W x h ∂rowMeasure ν (r + 1)) =
      partialFourierIntegral ψ ν Φ (adjacentRankKernelMatrix h) *
        glModelFunction ψ r σ ℓ W h⁻¹ * (χ (determinant h) : ℂ) *
          determinantWeight abv h ((r : ℂ) / 2) := by
  let f : (Fin (r + 1) → F.Carrier) → ℂ := fun y =>
    Φ (rectangularJoin h.val y) * ψ.complex (-((h⁻¹).val *ᵥ y) (Fin.last r))
  let C : ℂ := glModelFunction ψ r σ ℓ W h⁻¹ * (χ (determinant h) : ℂ)
  have hf : partialFourierIntegral ψ ν Φ (adjacentRankKernelMatrix h) =
      ∫ y, f y ∂rowMeasure ν (r + 1) := by
    simp only [partialFourierIntegral, rectangularFirstColumns_adjacentRankKernelMatrix,
      rectangularLastColumn_adjacentRankKernelMatrix, rowPairing, f, mulVec, dotProduct]
  have hp : ∀ x, integrand F ψ σ ℓ χ Φ W x h =
      f (h.val *ᵥ x) * C * determinantWeight abv h (((r + 2 : ℕ) : ℂ) / 2) := by
    intro x
    have hx : (h⁻¹).val *ᵥ (h.val *ᵥ x) = x := (columnHomeomorph F h).left_inv x
    dsimp only [integrand, f, C]
    rw [hx]
    ring
  simp_rw [hp]
  rw [integral_mul_const, integral_mul_const, integral_mulVec F ν h f, ← hf,
    Complex.real_smul, Complex.ofReal_inv]
  have hj := jacobian_detWeight F h
  dsimp only [C]
  calc
    _ = partialFourierIntegral ψ ν Φ (adjacentRankKernelMatrix h) *
        glModelFunction ψ r σ ℓ W h⁻¹ * (χ (determinant h) : ℂ) *
        ((F.canonicalTopologicalData.normalizedAbs h.val.det : ℂ)⁻¹ *
          determinantWeight abv h (((r + 2 : ℕ) : ℂ) / 2)) := by ring
    _ = _ := by rw [hj]

/-- Absolute convergence on the actual product measure above the uniform
square-matrix threshold. -/
theorem integrable_realTwist (ν : AdditiveHaarMeasure F.Carrier)
    (ψ : UnitaryAdditiveCharacter F.Carrier) {r : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (hσ : IsOfWhittakerType r (standardCharacter ψ r) σ) (ℓ : glFunctionals ψ r σ)
    (χ₀ : Quasicharacter F.Carrier) (u : ℝ)
    (hu : realTwistThreshold F ψ σ hσ ℓ χ₀ < u)
    (W : (glCoefficientModel ψ r σ ℓ).toSubmodule)
    (Φ : SchwartzBruhat (Matrix (Fin (r + 1)) (Fin (r + 2)) F.Carrier)) :
    Integrable (fun z => integrand F ψ σ ℓ (realTwistedCharacter F χ₀ u) Φ W z.1 z.2)
      ((rowMeasure ν (r + 1)).prod (generalLinearHaar F.Carrier r)) := by
  apply (integrable_prod_iff'
    (continuous_integrand F ψ σ hσ.1.1 ℓ _ Φ W).aestronglyMeasurable).mpr
  refine ⟨Filter.Eventually.of_forall (integrable_column F ν ψ σ ℓ _ Φ W), ?_⟩
  simpa only [integral_norm_column] using
    (integrable_realTwist_of_threshold F ν ψ σ hσ ℓ χ₀ u hu W (fiberNorm F ν r Φ)).norm

/-- Fubini and the exact column Fourier identity identify the literal JPSS
iterated integral with the partial-Fourier model integral. -/
theorem double_integral_eq_partialFourier (ν : AdditiveHaarMeasure F.Carrier)
    (ψ : UnitaryAdditiveCharacter F.Carrier) {r : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (hσ : IsOfWhittakerType r (standardCharacter ψ r) σ) (ℓ : glFunctionals ψ r σ)
    (χ₀ : Quasicharacter F.Carrier) (u : ℝ)
    (hu : realTwistThreshold F ψ σ hσ ℓ χ₀ < u)
    (W : (glCoefficientModel ψ r σ ℓ).toSubmodule)
    (Φ : SchwartzBruhat (Matrix (Fin (r + 1)) (Fin (r + 2)) F.Carrier)) :
    (∫ x, ∫ h, integrand F ψ σ ℓ (realTwistedCharacter F χ₀ u) Φ W x h
      ∂generalLinearHaar F.Carrier r ∂rowMeasure ν (r + 1)) =
    ∫ h, partialFourierIntegral ψ ν Φ (adjacentRankKernelMatrix h) *
      glModelFunction ψ r σ ℓ W h⁻¹ *
        (realTwistedCharacter F χ₀ u (determinant h) : ℂ) *
          determinantWeight abv h ((r : ℂ) / 2) ∂generalLinearHaar F.Carrier r := by
  rw [integral_integral_swap (integrable_realTwist F ν ψ σ hσ ℓ χ₀ u hu W Φ)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (integral_column_partialFourier F ν ψ σ ℓ _ Φ W)

/-- At an arbitrary ambient group element, the literal translated double integral
is the integral of the published actual tensor-model integrand. -/
theorem double_integral_eq_modelIntegrand (ν : AdditiveHaarMeasure F.Carrier)
    (ψ : UnitaryAdditiveCharacter F.Carrier) (hself : IsSelfDual ψ ν) {r : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (hσ : IsOfWhittakerType r (standardCharacter ψ r) σ) (ℓ : glFunctionals ψ r σ)
    (χ₀ : Quasicharacter F.Carrier) (u : ℝ)
    (hu : realTwistThreshold F ψ σ hσ ℓ χ₀ < u)
    (W : (glCoefficientModel ψ r σ ℓ).toSubmodule)
    (Φ : SchwartzBruhat (Matrix (Fin (r + 1)) (Fin (r + 2)) F.Carrier))
    (g : GeneralLinear (r + 2) F.Carrier) :
    (∫ x, ∫ h, integrand F ψ σ ℓ (realTwistedCharacter F χ₀ u)
      (rectangularTranslate g Φ) W x h
      ∂generalLinearHaar F.Carrier r ∂rowMeasure ν (r + 1)) =
    ∫ h, adjacentRankModelIntegrand ψ ν hself σ ℓ abv (realTwistedCharacter F χ₀ u)
      ((partialFourierEquiv ψ ν (r + 1) hself Φ) ⊗ₜ[ℂ] W) g h
        ∂generalLinearHaar F.Carrier r := by
  simpa only [adjacentRankModelIntegrand_tmul, rectangularRho0_intertwine,
    partialFourierEquiv_apply] using
    double_integral_eq_partialFourier F ν ψ σ hσ ℓ χ₀ u hu W (rectangularTranslate g Φ)

/-- Including the exact ambient character and modulus gives the published
adjacent-rank model integral itself. -/
theorem double_integral_eq_modelIntegral (ν : AdditiveHaarMeasure F.Carrier)
    (ψ : UnitaryAdditiveCharacter F.Carrier) (hself : IsSelfDual ψ ν) {r : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (hσ : IsOfWhittakerType r (standardCharacter ψ r) σ) (ℓ : glFunctionals ψ r σ)
    (χ₀ : Quasicharacter F.Carrier) (u : ℝ)
    (hu : realTwistThreshold F ψ σ hσ ℓ χ₀ < u)
    (W : (glCoefficientModel ψ r σ ℓ).toSubmodule)
    (Φ : SchwartzBruhat (Matrix (Fin (r + 1)) (Fin (r + 2)) F.Carrier))
    (g : GeneralLinear (r + 2) F.Carrier) :
    (realTwistedCharacter F χ₀ u (determinant g) : ℂ) *
      determinantWeight abv g (((r + 1 : ℕ) : ℂ) / 2) *
      (∫ x, ∫ h, integrand F ψ σ ℓ (realTwistedCharacter F χ₀ u)
        (rectangularTranslate g Φ) W x h
        ∂generalLinearHaar F.Carrier r ∂rowMeasure ν (r + 1)) =
    adjacentRankModelIntegral ψ ν hself σ ℓ abv (realTwistedCharacter F χ₀ u)
      (generalLinearHaar F.Carrier r)
      ((partialFourierEquiv ψ ν (r + 1) hself Φ) ⊗ₜ[ℂ] W) g := by
  rw [double_integral_eq_modelIntegrand F ν ψ hself σ hσ ℓ χ₀ u hu W Φ g]
  rfl

end Langlands.RankinSelberg.AdjacentDoubleIntegral
