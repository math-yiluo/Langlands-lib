import Langlands.Global.RankinSelberg.ComplexGodementStandardGaussians
import Langlands.Global.RankinSelberg.ComplexOrdinaryPolynomialKernel
import Langlands.Global.RankinSelberg.ComplexStandardGaussianFourier
import Langlands.Global.RankinSelberg.ComplexUnequalNormalizedSpan

/-! # Polynomial normalization for rectangular complex Godement tests -/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Operator SchwartzMap Langlands.Archimedean.ComplexDuality

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexAdjacentUnfolding

open ArchimedeanLocal Langlands.Archimedean Langlands.Automorphic Langlands.LocalFactor.Archimedean
open ComplexEqualPolynomialGeneration (IsGaussianPolynomialRow)
open ComplexTraceFourier (splitRowTransform_isGaussianPolynomialRow)
open ComplexGodementGaussianPolynomial (Coordinates gaussianPolynomial standardGaussianDilation
  standardMatrixTest standardColumnTest scalePolynomial complexGodementStandardGaussianSplit
  standardMatrixTest_eq_squarePolynomialGaussian standardColumnTest_isGaussianPolynomialRow)
open ComplexGodementColumnProduct (columnProduct)
open ComplexCharacterChange (centralCharacter)

attribute [local instance] archimedeanEquationComplexGLMeasurable
  archimedeanEquationComplexGLBorel archimedeanEquationComplexNMeasurable
  archimedeanEquationComplexNBorel archimedeanEquationComplexQMeasurable
  archimedeanEquationComplexQBorel

/-- Fixing the smaller coefficient gives a linear map from the larger function to
its ordinary unequal-rank kernel. -/
def complexUnequalOrdinaryKernel {r t : ℕ} (h : t < r)
    (V : Langlands.GeneralLinear (t + 1) ℂ → ℂ) :
    (Langlands.GeneralLinear (r + 1) ℂ → ℂ) →ₗ[ℂ]
      (ℂ → Langlands.RankinSelberg.LeftUnipotentQuotient t ℂ → ℂ) :=
  (LinearMap.fst ℂ _ _).comp ((complexUnequalKernelPair h).flip V)

@[simp] theorem complexUnequalOrdinaryKernel_apply {r t : ℕ} (h : t < r)
    (V : Langlands.GeneralLinear (t + 1) ℂ → ℂ) (W : Langlands.GeneralLinear (r + 1) ℂ → ℂ) :
    complexUnequalOrdinaryKernel h V W = complexUnequalIntegrand h W V := rfl

variable {r : ℕ}
local notation "G" => Langlands.GeneralLinear (r + 1) ℂ
local notation "G'" => Langlands.GeneralLinear (r + 2) ℂ
local notation "K" => unitaryCompact ℂ (r + 1)
local notation "Rect" => Matrix (Fin (r + 1)) (Fin (r + 2)) ℂ
local notation "Mat" => Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ
local notation "Vec" => Fin (r + 1) → ℂ
local notation "gap" => Nat.lt_succ_self r

/-- Under polynomiality for smaller equal-rank standard row tests, the ordinary integral
of every rectangular polynomial Gaussian Godement coefficient has polynomial normalization. -/
def ComplexAdjacentGodementPolynomialStatement : Prop :=
  ∀ (D : ComplexQuotientMeasureData r) [SFinite D.measure]
    (κ : Measure K) [IsFiniteMeasure κ] [κ.IsHaarMeasure]
    (a : ℂˣ), ‖(a : ℂ)‖ = 1 →
    ∀ (d : ComplexCharacterData) (ds : List ComplexCharacterData) (es : Fin (r + 1) → ComplexCharacterData),
    ds.length = r + 1 →
    ∀ (U : complexWhittakerModel r ds (-a))
      (B : complexStandardKFinite (r + 1) (List.ofFn es) →ₗ[ℂ] (G → ℂ)),
      IsComplexWhittakerIntertwiner r (List.ofFn es) a B →
    ∀ (v : complexStandardKFinite (r + 1) (List.ofFn es))
      (p : MvPolynomial (Coordinates (r + 1) (r + 2)) ℂ),
      (∀ (V : complexWhittakerModel r (List.ofFn es) a) (φ : 𝓢(Vec, ℂ)),
        IsGaussianPolynomialRow (2 * Real.pi) φ →
        ∃ (A : OrdinaryIntegralNormalization (complexEqualIntegral D U V φ)
          (fun s => ((complexPairLFactor ds (List.ofFn es)).denominator s)⁻¹)) (P : Polynomial ℂ),
          A.value = P.eval) →
    let W := godementTest D a d (gaussianPolynomial p) U.val
    complexUnequalIntegrand gap W (B v) ∈ polynomialOrdinaryKernels D.measure
      (fun s => ((complexPairLFactor (d :: ds) (List.ofFn es)).denominator s)⁻¹)

set_option maxHeartbeats 800000 in
theorem complexAdjacentGodementPolynomial : ComplexAdjacentGodementPolynomialStatement (r := r) := by
  intro D hD κ hκf hκh a ha d ds es hds U B hB v p hA W
  let : D.groupHaar.IsHaarMeasure := D.groupHaar_isHaar
  let Z := standardGaussianDilation
  let c := godementDilationMultiplier r d ds Z 0
  have hc : c ≠ 0 := by
    unfold c godementDilationMultiplier ArchimedeanLocal.detPower
    exact mul_ne_zero (mul_ne_zero (Units.ne_zero _) (Units.ne_zero _)) (Complex.exp_ne_zero _)
  let V : complexWhittakerModel r (List.ofFn es) a :=
    ⟨B v, Submodule.mem_iSup_of_mem B (Submodule.mem_iSup_of_mem hB ⟨v, rfl⟩)⟩
  let L (s : ℂ) := ((complexPairLFactor (d :: ds) (List.ofFn es)).denominator s)⁻¹
  let S := (polynomialOrdinaryKernels D.measure L).comap (complexUnequalOrdinaryKernel gap (B v))
  change W ∈ S
  obtain ⟨l, A, b, hsplit⟩ := complexGodementStandardGaussianSplit (r + 1) p
  let T (j : Fin l) := columnProduct (standardMatrixTest (A j)) (standardColumnTest (b j))
  have hTerm (j : Fin l) : godementTest D a d (T j) U.val ∈ S := by
    obtain ⟨N, P, hP⟩ := complexAdjacentJacquetPolynomial D κ a d ds es hds U B hB v
      (standardMatrixTest (A j)) (standardColumnTest (b j)) (scalePolynomial (A j))
      (standardMatrixTest_eq_squarePolynomialGaussian (A j))
      (fun V₁ => hA V₁ _ (splitRowTransform_isGaussianPolynomialRow a ha _
        (standardColumnTest_isGaussianPolynomialRow (b j))))
    have hI := splitTest_rightIntegrable D a d hds List.length_ofFn
      (standardMatrixTest (A j)) (standardColumnTest (b j)) U V
    exact mem_polynomialOrdinaryKernels_of_normalization N P hP hI
  have hTest : godementTest D a d (standardMatrixTest p) U.val ∈ S := by
    have h : godementTest D a d (standardMatrixTest p) U.val =
        ∑ j, godementTest D a d (T j) U.val := by
      rw [hsplit]
      funext g
      rw [Finset.sum_apply]
      exact godementTest_sum D a d T U g
    rw [h]
    exact S.sum_mem fun j _ => hTerm j
  have he : godementTest D a d (standardMatrixTest p) U.val = c • W := by
    funext g
    exact continuedValue_dilateMatrixTest D.groupHaar (complexSelfDualMeasure a) a d hds U Z
      (gaussianPolynomial p) g 0
  rw [he] at hTest
  have hi := S.smul_mem c⁻¹ hTest
  rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at hi

end Langlands.Global.RankinSelbergGlobal.ComplexAdjacentUnfolding
