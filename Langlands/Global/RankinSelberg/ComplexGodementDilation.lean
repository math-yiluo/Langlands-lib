import Langlands.Global.RankinSelberg.ComplexAdjacentGaussianStripGrowth
import Langlands.Representation.GodementJacquet.ComplexJacquetDeterminantWeight

/-! # Dilation of complex Godement tests and their strip estimate -/

noncomputable section

open MeasureTheory Set
open scoped Matrix.Norms.Operator SchwartzMap Langlands.Archimedean.ComplexDuality

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexAdjacentUnfolding

open ArchimedeanLocal Langlands.Archimedean Langlands.GeneralLinear
open Langlands.LocalFactor.Archimedean Langlands.HarmonicAnalysis
open Langlands.Analysis.SchwartzMatrixNorm (operatorToEntry operatorToEntry_apply)
open Langlands.GodementJacquet (detPower_complex_mul)
open ComplexGodementAddedCharacter (continuedValue rightTest rightTest_apply)
open ComplexGodementColumnChange (columnIntegral iteratedKernel)
open ComplexCharacterChange (centralCharacter model_mul_scalar)
open ComplexGodementGaussianPolynomial (Coordinates gaussianPolynomial)

attribute [local instance] archimedeanEquationComplexGLMeasurable
  archimedeanEquationComplexGLBorel archimedeanEquationComplexNMeasurable
  archimedeanEquationComplexNBorel archimedeanEquationComplexQMeasurable
  archimedeanEquationComplexQBorel

variable {r : ℕ}
local notation "G" => Langlands.GeneralLinear (r + 1) ℂ
local notation "G'" => Langlands.GeneralLinear (r + 2) ℂ
local notation "Kc" => unitaryCompact ℂ (r + 1)
local notation "Rect" => Matrix (Fin (r + 1)) (Fin (r + 2)) ℂ
local notation "Vec" => Fin (r + 1) → ℂ
local notation "gap" => Nat.lt_succ_self r

/-- Pull back a complex matrix Schwartz function by nonzero scalar dilation. -/
def dilateMatrixTest {m n : ℕ} (z : ℂˣ) (Φ : 𝓢(Matrix (Fin m) (Fin n) ℂ, ℂ)) :
    𝓢(Matrix (Fin m) (Fin n) ℂ, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (((ContinuousLinearEquiv.smulLeft (R₁ := ℂ) (M₁ := Matrix (Fin m) (Fin n) ℂ)) z).restrictScalars ℝ) Φ

@[simp]
theorem dilateMatrixTest_apply {m n : ℕ} (z : ℂˣ) (Φ : 𝓢(Matrix (Fin m) (Fin n) ℂ, ℂ))
    (X : Matrix (Fin m) (Fin n) ℂ) :
    dilateMatrixTest z Φ X = Φ ((z : ℂ) • X) := rfl

private theorem rectangularJoin_scalar (z : ℂˣ) (h : G) (v : Vec) :
    rectangularJoin ((GeneralLinear.scalar z : G) * h).val
        (((GeneralLinear.scalar z : G) * h).val.mulVec v) =
      (z : ℂ) • rectangularJoin h.val (h.val.mulVec v) := by
  have hS : ((GeneralLinear.scalar z : G) * h).val = (z : ℂ) • h.val := by
    change Matrix.scalar (Fin (r + 1)) (z : ℂ) * h.val = _
    rw [Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]
  rw [hS, Matrix.smul_mulVec]
  ext i j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simp only [rectangularJoin_last, Matrix.smul_apply, Pi.smul_apply]
  · simp only [rectangularJoin_castSucc, Matrix.smul_apply]

/-- The multiplier for a dilated rectangular test at a fixed added exponent. -/
def godementDilationMultiplier (r : ℕ) (d : ComplexCharacterData) (ds : List ComplexCharacterData)
    (z : ℂˣ) (s : ℂ) : ℂ :=
  let Z := (GeneralLinear.scalar z : Langlands.GeneralLinear (r + 1) ℂ)⁻¹
  (centralCharacter ds z : ℂ) * (d.character (determinant Z) : ℂ) *
    ArchimedeanLocal.detPower complexNormalizedAbs Z ((((r + 1 : ℕ) + 1 : ℂ) / 2) + s)

/-- Dilation acts on a continued Godement value through the smaller model's central
character and the determinant weight of the scalar change of variable. -/
theorem continuedValue_dilateMatrixTest (ν : Measure G) [ν.IsMulLeftInvariant]
    (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ) (d : ComplexCharacterData)
    {ds : List ComplexCharacterData} (hds : ds.length = r + 1)
    (U : complexWhittakerModel r ds (-a)) (z : ℂˣ) (Φ : 𝓢(Rect, ℂ)) (g : G') (s : ℂ) :
    continuedValue ν μ d a (operatorToEntry (dilateMatrixTest z Φ)) U.val g s =
      godementDilationMultiplier r d ds z s * continuedValue ν μ d a (operatorToEntry Φ) U.val g s := by
  let Z : G := GeneralLinear.scalar z
  let χ := complexScaledCharacter a
  let Ψ := rightTest g (operatorToEntry Φ)
  let Ψz := rightTest g (operatorToEntry (dilateMatrixTest z Φ))
  let t : ℂ := (((r + 1 : ℕ) + 1 : ℂ) / 2) + s
  let C := godementDilationMultiplier r d ds z s
  have hColumn (h : G) : columnIntegral χ μ Ψz h = columnIntegral χ μ Ψ (Z * h) := by
    unfold columnIntegral
    refine integral_congr_ae (ae_of_all _ fun v => ?_)
    simp only [Ψz, Ψ, rightTest_apply, operatorToEntry_apply, dilateMatrixTest_apply]
    rw [show rectangularJoin (Z * h).val ((Z * h).val.mulVec v) =
      (z : ℂ) • rectangularJoin h.val (h.val.mulVec v) from rectangularJoin_scalar z h v,
      Matrix.smul_mul]
  let F := iteratedKernel χ μ d Ψ U.val t
  let Fz := iteratedKernel χ μ d Ψz U.val t
  have hF (h : G) : Fz (Z⁻¹ * h) = C * F h := by
    have hU : U.val ((Z⁻¹ * h)⁻¹) = (centralCharacter ds z : ℂ) * U.val h⁻¹ := by
      rw [mul_inv_rev, inv_inv]
      exact model_mul_scalar hds U.2 z h⁻¹
    have hZ (h : G) : Z * (Z⁻¹ * h) = h := by simp
    simp only [Fz, F, iteratedKernel, hColumn, hZ, hU, map_mul, Units.val_mul,
      detPower_complex_mul, C, godementDilationMultiplier, ← show Z = GeneralLinear.scalar z from rfl]
    ring
  have hInt : (∫ h, Fz h ∂ν) = C * ∫ h, F h ∂ν := by
    rw [← integral_mul_left_eq_self Fz Z⁻¹]
    simp_rw [hF, integral_const_mul]
  unfold continuedValue
  change _ * (∫ h, Fz h ∂ν) = C * (_ * ∫ h, F h ∂ν)
  rw [hInt]
  ring

/-- The adjacent Gaussian-polynomial strip estimate also holds after any fixed nonzero
dilation of the rectangular test. -/
def ComplexAdjacentDilatedGaussianStripGrowthStatement : Prop :=
  ∀ (D : ComplexQuotientMeasureData r) [SFinite D.measure]
    (κ : Measure Kc) [IsFiniteMeasure κ] [κ.IsHaarMeasure]
    (a : ℂˣ) (d : ComplexCharacterData)
    (ds : List ComplexCharacterData) (es : Fin (r + 1) → ComplexCharacterData),
    ds.length = r + 1 →
  ∀ (U : complexWhittakerModel r ds (-a)) (V : complexWhittakerModel r (List.ofFn es) a)
    (p : MvPolynomial (Coordinates (r + 1) (r + 2)) ℂ) (z : ℂˣ),
    (∀ (V₁ : complexWhittakerModel r (List.ofFn es) a) (ψ : 𝓢(Vec, ℂ)),
      ∃ A : OrdinaryIntegralNormalization (complexEqualIntegral D U V₁ ψ)
        (fun s => ((complexPairLFactor ds (List.ofFn es)).denominator s)⁻¹),
        HasStripExponentialGrowth A.value) →
    let W (g : G') := continuedValue D.groupHaar (complexSelfDualMeasure a) d a
      (operatorToEntry (dilateMatrixTest z (gaussianPolynomial p))) U.val g 0
    ∃ R : OrdinaryIntegralNormalization (complexUnequalIntegral gap D W V)
      (fun s => ((complexPairLFactor (d :: ds) (List.ofFn es)).denominator s)⁻¹),
      HasStripExponentialGrowth R.value ∧
      ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → Integrable (complexUnequalIntegrand gap W V s) D.measure

theorem complexAdjacentDilatedGaussianStripGrowth :
    ComplexAdjacentDilatedGaussianStripGrowthStatement (r := r) := by
  intro D _ κ _ _ a d ds es hds U V p z hA W
  let W₀ (g : G') := continuedValue D.groupHaar (complexSelfDualMeasure a) d a
    (operatorToEntry (gaussianPolynomial p)) U.val g 0
  let : D.groupHaar.IsHaarMeasure := D.groupHaar_isHaar
  let c := godementDilationMultiplier r d ds z 0
  have hW (g : G') : W g = c * W₀ g :=
    continuedValue_dilateMatrixTest D.groupHaar (complexSelfDualMeasure a) a d hds U z
      (gaussianPolynomial p) g 0
  have hK (s : ℂ) : complexUnequalIntegrand gap W V s =
      fun q => c * complexUnequalIntegrand gap W₀ V s q := by
    funext q
    simp only [complexUnequalIntegrand, ArchimedeanLocal.unequalIntegrand, hW, mul_assoc]
  obtain ⟨R, hR, σ, hσ⟩ := complexAdjacentGaussianStripGrowth D κ a d ds es hds U V p hA
  obtain ⟨τ, hτ⟩ := R.eq_on_right
  have hc : HasStripExponentialGrowth (fun _ => c) :=
    fun _ _ => ⟨‖c‖, 0, 0, norm_nonneg _, le_rfl, fun _ _ _ _ => by simp⟩
  refine ⟨⟨fun s => c * R.value s, fun s hs => analyticAt_const.fun_mul (R.analytic s hs),
    ⟨τ, fun s hs => ?_⟩⟩, hc.mul hR, σ, fun s hs => ?_⟩
  · change (∫ q, complexUnequalIntegrand gap W V s q ∂D.measure) =
      (c * R.value s) * _
    rw [hK s, integral_const_mul]
    change c * complexUnequalIntegral gap D W₀ V s = _
    rw [hτ s hs, mul_assoc]
  · rw [hK s]
    exact (hσ s hs).const_mul c

end Langlands.Global.RankinSelbergGlobal.ComplexAdjacentUnfolding
