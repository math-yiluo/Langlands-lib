import Langlands.Global.RankinSelberg.ComplexGapLeadingGaussianFamily
import Langlands.Global.RankinSelberg.ComplexGapSquareDilation
import Langlands.Global.RankinSelberg.ComplexGapRetainedFiber
import Langlands.Global.RankinSelberg.ComplexUnequalSmallerNormalization
import Langlands.Global.RankinSelberg.ComplexPlaceUnequalFunctionalEquationProof

/-! # Entire normalized values on the retained gap chart -/

noncomputable section

open MeasureTheory Set
open scoped Matrix.Norms.Operator SchwartzMap Langlands.Archimedean.ComplexDuality

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGapRetained

open ArchimedeanLocal Langlands.Archimedean Langlands.Automorphic Langlands.GeneralLinear
open Langlands.Archimedean.ComplexGeneralLinearHaarDensity (complexGeneralLinearHaar)
open Langlands.Analysis.SchwartzMatrixNorm (operatorToEntry)
open Langlands.LocalFactor.Archimedean
open Langlands.RankinSelberg (LeftUnipotentQuotient)
open ComplexAdjacentUnfolding (splitSquareTransform dilateMatrixTest_apply)
open ComplexGapDualChart (retainedTail)
open ComplexGapLeadingFourier (stackRows stackRows_left stackRows_right)
open ComplexGapLeadingHaar (Retained outerWithLeading)
open ComplexGapLeadingCompact (complexGapLeadingGaussianFamily exists_standardMatrixTest_polynomialGaussian)
open ComplexGapRankCoordinates (rankLT)
open ComplexGapSquareAverage (squareKernel)
open ComplexGapSquareReflection (leadingSquareTest leadingSquareTest_apply leadingSquareTest_finite
  squareDilationWeight differentiable_squareDilationWeight continuous_squareDilationWeight stripGrowth_squareDilationWeight
  complexGapSquareDilation)
open ComplexGapTriangularChart (Outer continuous_packedTail)
open ComplexGapUnitDeterminant (normalizingScalar continuous_unitRetained)
open ComplexGodementGaussianPolynomial (Coordinates gaussianPolynomial standardGaussianDilation standardMatrixTest)
open ComplexJacquet (HasComplexPairNormalizedGrowth HasSquareConvolutionTrace complexSquareZetaConvolution)
open ComplexSquareZeta (squarePolynomialGaussian)
open ComplexWeightedKernelReflection (pairReflectionFactor)

attribute [local instance] archimedeanEquationComplexGLMeasurable archimedeanEquationComplexGLBorel
  archimedeanEquationComplexNMeasurable archimedeanEquationComplexNBorel
  archimedeanEquationComplexQMeasurable archimedeanEquationComplexQBorel

variable (t q : ℕ)
local notation "k" => t + 1
local notation "r" => t + 1 + q
local notation "n" => t + 1 + q + 1
local notation "G" => fun m => Langlands.GeneralLinear m ℂ
local notation "H" => G (t + 1)
local notation "K" => fun m => unitaryCompact ℂ m
local notation "M" => fun i j => Matrix (Fin i) (Fin j) ℂ
local notation "KF[" es "]" => complexStandardKFinite k es
local notation "ν" => complexGeneralLinearHaar k
local notation "ι" => inverseTranspose k ℂ
local notation "ρ" => ArchimedeanLocal.translateFunction

/-- The coordinates left after integrating the leading group and the lower-rank variables. -/
abbrev RetainedPoint := Retained k q × Langlands.GeneralLinear.upperUnipotent (q + 1) ℂ

/-- The group matrix corresponding to a retained point. -/
def retainedGroup (p : RetainedPoint t q) : G n :=
  retainedTail k q (outerWithLeading k q 1 p.1) p.2

theorem continuous_retainedGroup : Continuous (retainedGroup t q) := by
  have hY : Continuous (fun p : RetainedPoint t q => outerWithLeading k q 1 p.1) := by
    unfold outerWithLeading
    fun_prop
  exact ((continuous_unitRetained k q).comp hY).mul
    ((continuous_packedTail k q).comp (continuous_const.prodMk continuous_snd))

private theorem continuous_retainedScalar :
    Continuous (fun p : RetainedPoint t q => normalizingScalar k q p.1.1.1) := by
  apply (Units.isOpenEmbedding_val (R := ℂ)).isEmbedding.continuous_iff.mpr
  change Continuous (fun p : RetainedPoint t q => (Real.exp (-(∑ i, p.1.1.1 i) / ((k : ℕ) : ℝ)) : ℂ))
  exact Complex.continuous_ofReal.comp (Real.continuous_exp.comp (by fun_prop))

private theorem leadingStandard_finite (Y : Outer k q) (z : Langlands.GeneralLinear.upperUnipotent (q + 1) ℂ)
    (p : MvPolynomial (Coordinates n k) ℂ) :
    let C := retainedTail k q Y z
    let Φ := leadingSquareTest t q C (operatorToEntry (standardMatrixTest p))
    FiniteDimensional ℂ (Submodule.span ℂ (range fun u : K k => fun X : M k k => Φ (u.val⁻¹.val * X))) := by
  intro C Φ
  let u₀ : ℂ := standardGaussianDilation
  let Ψ := leadingSquareTest t q C (operatorToEntry (gaussianPolynomial p))
  have hΦ (X : M k k) : Φ X = Ψ (u₀ • X) := by
    rw [show Φ X = standardMatrixTest p (C.val * stackRows k (q + 1) k X 0) from rfl,
      standardMatrixTest, dilateMatrixTest_apply]
    change gaussianPolynomial p (u₀ • (C.val * stackRows k (q + 1) k X 0)) =
      gaussianPolynomial p (C.val * stackRows k (q + 1) k (u₀ • X) 0)
    congr 1
    rw [← Matrix.mul_smul]
    congr 1
    ext i j
    refine Fin.addCases (m := k) («n» := q + 1) (fun i₀ => ?_) (fun i₁ => ?_) i
    · simp only [Matrix.smul_apply, stackRows_left]
    · simp only [Matrix.smul_apply, stackRows_right, Matrix.zero_apply, smul_zero]
  let L : (M k k → ℂ) →ₗ[ℂ] (M k k → ℂ) :=
    { toFun := fun F X => F (u₀ • X), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let E := Submodule.span ℂ (range fun u : K k => fun X : M k k => Ψ (u.val⁻¹.val * X))
  let : FiniteDimensional ℂ E := leadingSquareTest_finite t q Y z p
  apply Submodule.finiteDimensional_of_le (S₂ := E.map L)
  apply Submodule.span_le.mpr
  rintro _ ⟨u, rfl⟩
  refine ⟨_, Submodule.subset_span ⟨u, rfl⟩, ?_⟩
  funext X
  change Ψ (u.val⁻¹.val * (u₀ • X)) = Φ (u.val⁻¹.val * X)
  rw [hΦ, Matrix.mul_smul]

private theorem stripGrowth_polynomial (p : Polynomial ℂ) : HasStripExponentialGrowth p.eval := by
  have hid : HasStripExponentialGrowth (fun z : ℂ => z) := by
    intro a b
    let B := |a| + |b| + 1
    refine ⟨B, 1, 0, by positivity, zero_le_one, fun z ha hb _ => ?_⟩
    rw [one_mul]
    have hR : |z.re| ≤ |a| + |b| := by
      rw [abs_le]
      constructor <;> linarith [neg_abs_le a, le_abs_self b, abs_nonneg a, abs_nonneg b]
    calc
      ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im _
      _ ≤ B * (|z.im| + 1) := by nlinarith [abs_nonneg z.im, abs_nonneg a, abs_nonneg b]
      _ ≤ B * Real.exp |z.im| := mul_le_mul_of_nonneg_left (Real.add_one_le_exp _) (by positivity)
  have hpow : ∀ j : ℕ, HasStripExponentialGrowth (fun z : ℂ => z ^ j) := by
    intro j
    induction j with
    | zero => simpa only [pow_zero] using HasStripExponentialGrowth.const 1
    | succ j ih => simpa only [pow_succ, Pi.mul_def] using ih.mul hid
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [Polynomial.eval_add, Pi.add_def] using hp.add hq
  | monomial j c => simpa only [Polynomial.eval_monomial] using (hpow j).const_mul c

/-- A standard rectangular leading test yields a continuous family of entire normalized
retained integrals. On a right half-plane for each retained point, its two endpoint identities
recover the ordinary and reflected product integrals whenever the respective kernel is integrable. -/
def ComplexGapRetainedNormalizationStatement : Prop :=
  ∀ (a : ℂˣ) (d : ComplexCharacterData) (ds : List ComplexCharacterData) (_hds : ds.length = r + 1)
    (e : Fin k → ComplexCharacterData) (D : ComplexQuotientMeasureData t),
    let es := List.ofFn e
    ∀ (W : complexWhittakerModel r ds (-a)) (B : KF[es] →ₗ[ℂ] (H → ℂ)),
      IsComplexWhittakerIntertwiner t es a B →
      ∃ A : G n → KF[es] →ₗ[ℂ] (ℂ → ℂ),
        (∀ v, Differentiable ℂ (A 1 v) ∧ ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
          Integrable (complexUnequalIntegrand (rankLT t q) W.val (B v) s) D.measure ∧
          A 1 v s = (complexPairLFactor ds es).denominator s *
            complexUnequalIntegral (rankLT t q) D W.val (B v) s) ∧
        ∀ (p : MvPolynomial (Coordinates n k) ℂ) (f : KF[es]),
          let χ (x : RetainedPoint t q) := leadingSquareTest t q (retainedGroup t q x) (operatorToEntry (standardMatrixTest p))
          let U (x : RetainedPoint t q) := ρ (retainedGroup t q x)⁻¹ W.val
          let E (s : ℂ) := pairReflectionFactor ds es (-a) (complexCentralSign es ^ r) s *
            pairReflectionFactor [d] es a 1 s
          ∃ (Y : RetainedPoint t q → ℂ → KF[es]) (J : RetainedPoint t q → ℂ → ℂ),
            (∀ s, Continuous (fun x => J x s)) ∧
            (∀ x, Differentiable ℂ (J x) ∧ HasStripExponentialGrowth (J x)) ∧
            ∀ x, ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
              (∀ g : H, (complexPairLFactor [d] es).denominator s *
                (∫ z, squareKernel d (χ x) (fun h => B f (g * h)) s z ∂ν) = B (Y x s) g) ∧
              J x s = (complexPairLFactor ds es).denominator s * complexUnequalIntegral (rankLT t q) D (U x) (B (Y x s)) s ∧
              (Integrable (ordinaryFiber (rankLT t q) d (χ x) (U x) (B f) s) (D.measure.prod ν) →
                (complexPairLFactor (d :: ds) es).denominator s *
                  (∫ y, ordinaryFiber (rankLT t q) d (χ x) (U x) (B f) s y ∂D.measure.prod ν) = J x s) ∧
              (Integrable (reflectedFiber (rankLT t q) a d (χ x) (U x) (B f) s)
                  ((complexUnequalDualMeasure (-a) D).prod ν) →
                (complexPairLFactor ((d :: ds).map ComplexCharacterData.inv) (es.map ComplexCharacterData.inv)).denominator s *
                  (∫ y, reflectedFiber (rankLT t q) a d (χ x) (U x) (B f) s y ∂(complexUnequalDualMeasure (-a) D).prod ν) =
                  E (1 - s) * J x (1 - s))

set_option maxHeartbeats 1800000 in
theorem complexGapRetainedNormalization : ComplexGapRetainedNormalizationStatement t q := by
  intro a d ds hds e D es W B hB
  have hes : es.length = k := List.length_ofFn
  have hGrowth (W₀ : complexWhittakerModel r ds (-a)) (V₀ : complexWhittakerModel t es (-(-a))) :=
    complexUnequalNormalizedGrowth r t (rankLT t q) ds es hds hes (-a) D W₀.val V₀.val W₀.2 V₀.2
  have hB' : IsComplexWhittakerIntertwiner t es (-(-a)) B := by simpa only [neg_neg] using hB
  obtain ⟨A, hAc, hA⟩ := complexUnequalSmallerNormalization (rankLT t q) ds es hds hes (-a) D hGrowth W B hB'
  refine ⟨A, fun v => ?_, ?_⟩
  · obtain ⟨hD, _, ⟨σ, hσ⟩⟩ := hA 1 v
    refine ⟨hD, σ, fun s hs => ?_⟩
    obtain ⟨hi, _, he, _⟩ := hσ s hs
    have hOne : ρ (1 : G n) W.val = W.val := by
      funext g
      change W.val (g * 1) = W.val g
      rw [mul_one]
    rw [hOne] at hi he
    exact ⟨hi, he⟩
  intro p f χ U E
  classical
  obtain ⟨l, c, P, hc, hP⟩ := complexGapLeadingGaussianFamily t q p
  choose pj hpj using fun j => exists_standardMatrixTest_polynomialGaussian (P j)
  let Φj (j : Fin l) : 𝓢(M k k, ℂ) := standardMatrixTest (pj j)
  have hΦj (j : Fin l) : (Φj j : M k k → ℂ) = squarePolynomialGaussian (P j) := funext (hpj j)
  choose F hF hTrace using fun j => complexSquareZetaConvolution ν d e (Φj j) (P j) (hΦj j) a B hB f
  have hT (j : Fin l) : HasSquareConvolutionTrace ν d e B (Φj j) f (F j) := ⟨(hF j).1, hTrace j⟩
  choose m p₀ v₀ hv₀ using fun j => (hT j).1
  let L := Σ j : Fin l, Fin (m j)
  let v (j : L) := v₀ j.1 j.2
  let w (x : RetainedPoint t q) := squareDilationWeight t d es (normalizingScalar k q x.1.1.1)
  let β (x : RetainedPoint t q) (j : L) (s : ℂ) := w x s * c j.1 x.1.1.2 * (p₀ j.1 j.2).eval s
  let Y (x : RetainedPoint t q) (s : ℂ) := ∑ j : L, β x j s • v j
  have hY (x : RetainedPoint t q) (s : ℂ) : Y x s = w x s • ∑ j, c j x.1.1.2 • F j s := by
    calc
      Y x s = ∑ j : Fin l, ∑ i : Fin (m j), β x ⟨j, i⟩ s • v ⟨j, i⟩ :=
        Fintype.sum_sigma (fun j : L => β x j s • v j)
      _ = _ := by
        simp [Finset.smul_sum, hv₀, smul_smul, β, v, mul_assoc]
  let J (x : RetainedPoint t q) (s : ℂ) := A (retainedGroup t q x)⁻¹ (Y x s) s
  have hJ (x : RetainedPoint t q) (s : ℂ) : J x s = ∑ j : L, β x j s * A (retainedGroup t q x)⁻¹ (v j) s := by
    simp only [J, Y, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine ⟨Y, J, fun s => ?_, fun x => ?_, fun x => ?_⟩
  · simp_rw [hJ]
    apply continuous_finsetSum
    intro j _
    exact ((((continuous_squareDilationWeight t d es s).comp (continuous_retainedScalar t q)).mul
      ((hc j.1).comp (continuous_snd.comp (continuous_fst.comp continuous_fst)))).mul continuous_const).mul
      ((hAc (v j) s).comp ((continuous_retainedGroup t q).inv))
  · rw [show J x = (fun s => ∑ j : L, β x j s * A (retainedGroup t q x)⁻¹ (v j) s) from funext (hJ x)]
    constructor
    · apply Differentiable.fun_sum
      intro j _
      exact ((((differentiable_squareDilationWeight t d es _).mul_const _).mul
        (p₀ j.1 j.2).differentiable)).mul (hA _ _).1
    · apply HasStripExponentialGrowth.fun_sum
      intro j _
      exact ((((stripGrowth_squareDilationWeight t d es _).mul (HasStripExponentialGrowth.const _)).mul
        (stripGrowth_polynomial (p₀ j.1 j.2)))).mul (hA _ _).2.1
  · let x₀ := outerWithLeading k q 1 x.1
    obtain ⟨b, hb⟩ := complexGapSquareDilation t ν (ComplexDuality.unitaryHaar k) a d e B hB f l
      (χ x) Φj F (fun j => c j x.1.1.2) (normalizingScalar k q x.1.1.1) hT
      (fun X => by
        rw [show χ x X = leadingSquareTest t q (retainedTail k q x₀ x.2)
          (operatorToEntry (standardMatrixTest p)) X from rfl, hP]
        simp only [hΦj, outerWithLeading, x₀])
      (leadingStandard_finite t q x₀ x.2 p)
    obtain ⟨b', hb'⟩ := smallerNormalization_finiteFamily (rankLT t q) ds es (-a) D (U x) B
      (A (retainedGroup t q x)⁻¹) v (β x) (fun j => (hA _ _).2.2)
    refine ⟨max b b', fun s hs => ?_⟩
    have hs₁ := (le_max_left b b').trans_lt hs
    have hs₂ := (le_max_right b b').trans_lt hs
    have hO (g : H) : (complexPairLFactor [d] es).denominator s *
        (∫ z, squareKernel d (χ x) (fun h => B f (g * h)) s z ∂ν) = B (Y x s) g := by
      rw [hY x s]
      exact (hb s hs₁ g).1
    have hR (g : H) : (complexPairLFactor [d.inv] (es.map ComplexCharacterData.inv)).denominator s *
        (∫ z, squareKernel d.inv (splitSquareTransform a (χ x)) (fun h => B f (g * ι h)) s z ∂ν) =
        pairReflectionFactor [d] es a 1 (1 - s) * B (Y x (1 - s)) g := by
      rw [hY x (1 - s)]
      exact (hb s hs₁ g).2
    have hJ₀ := (hb' s hs₂).1
    have hJ₁ := (hb' s hs₂).2
    have hμ : @complexUnequalDualMeasure r t (-a) D = @complexUnequalDualMeasure r t a D := by
      unfold complexUnequalDualMeasure
      rw [Langlands.GodementJacquet.complexSelfDualMeasure_neg_scale]
    obtain ⟨ho, hd⟩ := complexGapRetainedFiber (rankLT t q) a d ds es D (χ x) (U x) (B f)
      (B (Y x s)) (B (Y x (1 - s))) s (pairReflectionFactor [d] es a 1 (1 - s))
    refine ⟨hO, hJ₀, fun hi => (ho hi hO).trans hJ₀.symm, fun hi => ?_⟩
    rw [hμ] at hi ⊢
    rw [hμ] at hJ₁
    rw [hd hi hR, ← hJ₁]
    unfold E J
    ring

end Langlands.Global.RankinSelbergGlobal.ComplexGapRetained
