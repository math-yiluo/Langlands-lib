import Langlands.Representation.RankinSelberg.TwoBlockDominantStrictFactors
import Langlands.Representation.RankinSelberg.TwoBlockDominantStrictEntireSlices
import Langlands.Representation.RankinSelberg.TwoBlockDominantEqualLContinuation
import Langlands.Representation.RankinSelberg.TwoBlockDominantFirstBlockLaurentIdentityProof

noncomputable section

namespace Langlands.RankinSelberg.DominantRankTransport

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration
  Polynomial TwoBlockLowerUnipotentQuotient

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance strictLContinuationTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance strictLContinuationValuation : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance strictLContinuationLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance strictLContinuationT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance strictLContinuationSecondCountable : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance strictLContinuationSigmaCompact : SigmaCompactSpace F.Carrier :=
  F.canonicalTopologicalData.sigmaCompactSpace
local instance strictLContinuationMeasurable : MeasurableSpace F.Carrier := borel _
local instance strictLContinuationBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance strictLContinuationGLMeasurable (n : ℕ) :
    MeasurableSpace (GeneralLinear (n + 1) F.Carrier) := borel _
local instance strictLContinuationGLBorel (n : ℕ) :
    BorelSpace (GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
local instance strictLContinuationUnipotentMeasurable (n : ℕ) :
    MeasurableSpace (upperUnipotent (n + 1) F.Carrier) := borel _
local instance strictLContinuationUnipotentBorel (n : ℕ) :
    BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
local instance strictLContinuationQuotientMeasurable (n : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient n F.Carrier) := borel _
local instance strictLContinuationQuotientBorel (n : ℕ) :
    BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩

local notation "qF" => F.canonicalTopologicalData.residueCardinality
local notation "abv" => normalizedAbsoluteValue F.canonicalTopologicalData

open ParameterSpecialization HarmonicAnalysis.BilateralLaurentSeries
open AdjacentGammaContinuation

section Coefficients

variable {n r j k : ℕ} (hr : r = n + (j + k + 1))
  (ψ : UnitaryAdditiveCharacter F.Carrier)
  (μ : Measure (LeftUnipotentQuotient n F.Carrier))
  (ν : AdditiveHaarMeasure F.Carrier)
  [Measure.IsMulRightInvariant (unipotentHaar F.Carrier n)]
  (hμ : IsCompatible (upperUnipotent (n + 1) F.Carrier)
    (generalLinearHaar F.Carrier n) (unipotentHaar F.Carrier n) μ)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {U : Type uW} [AddCommGroup U] [Module ℂ U]
  (π : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
  (τ : Representation ℂ (GeneralLinear (n + 1) F.Carrier) U)
  (hπ : IsOfWhittakerType r (standardCharacter ψ r) π)
  (hτ : IsOfWhittakerType n (inverseStandardCharacter ψ n) τ)
  (lambda : glFunctionals ψ r π) (ell : glInverseFunctionals ψ n τ)
  (hlambda : lambda.val ≠ 0) (hell : ell.val ≠ 0)
  (f : (coefficientModel π lambda).toSubmodule)
  (f' : (coefficientModel τ ell).toSubmodule)

include hμ hπ hτ hlambda hell

/-- Rational continuation and absolute spectral expansion of the same actual
supplied-Haar strict integral. -/
theorem strictRankCoefficient_continuationData :
    ∃ R : RationalFunctions,
      HasRationalContinuation qF
        (unequalRankIntegralAt j k hr ψ abv μ (rectangularMeasure ν j (n + 1))
          f.val f'.val) R ∧
      HasAbsoluteBilateralSpectralExpansion qF
        (strictSliceCoefficient F hr ψ μ ν f.val f'.val)
        (unequalRankIntegralAt j k hr ψ abv μ (rectangularMeasure ν j (n + 1))
          f.val f'.val) := by
  obtain ⟨-, R, hR⟩ := strictCoefficient_continuationData F hr ψ μ ν π τ lambda ell
    hμ hπ hτ hlambda hell f f'
  have han := strictRankAnalyticAt F hr ψ μ ν π τ lambda ell
    hμ hπ hτ hlambda hell
  subst r
  obtain ⟨Cbound, hC⟩ := han.1 f f'
  refine ⟨R, hR, Cbound, fun s hs => ?_⟩
  have hexp := (unequalRankSliceExpansion_of_converges F j k ψ μ
    (strictRectangleMeasure F ν j (n + 1)) f.val f'.val s (hC s hs)).2
  have hI := congrFun (strictIntegral_eq F rfl ψ μ ν f.val f'.val) s
  exact ⟨hexp.1, hI ▸ hexp.2⟩

/-- A complete symmetric L certificate and its polynomial bound clear every
literal strict coefficient, by scalar spectral uniqueness. -/
theorem strictRankCoefficient_clearing_of_certificate
    (νSD : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    (P A : Polynomial ℂ) (hA : A ≠ 0)
    (hP : IsPadicSymmetricLPolynomial F ψ νSD.val π τ P)
    (hdiv : ∃ (Q : Polynomial ℂ) (e : ℕ), X ^ e * A = Q * P) :
    ∃ L : LaurentPolynomial ℂ, ofLaurentPolynomial L =
      A.toLaurent • strictSliceCoefficient F hr ψ μ νSD.val f.val f'.val := by
  have hnr : n < r := by omega
  have hgen := (isPairLPolynomial_of_lt hnr).mp
    (((isPadicSymmetricLPolynomial_of_le hnr.le).mp hP).2 μ hμ) j k hr
  have hspan : Submodule.span LaurentCoefficients
      {(algebraMap (Polynomial ℂ) RationalFunctions P)⁻¹} ≤
      Submodule.span LaurentCoefficients
        {(algebraMap (Polynomial ℂ) RationalFunctions A)⁻¹} :=
    (Submodule.span_singleton_le_iff_mem _ _).mpr
      ((reciprocalLaurentSpanClearing P A hgen.polynomial_ne_zero hA).mpr hdiv)
  obtain ⟨R, hR, ha⟩ := strictRankCoefficient_continuationData F hr ψ μ νSD.val hμ
    π τ hπ hτ lambda ell hlambda hell f f'
  subst r
  have han := unequalRankAnalytic F F.canonicalTopologicalData n j k ψ μ hμ
    νSD.val V U π τ hπ hτ lambda ell hlambda hell
  have hmem : R ∈ Submodule.span LaurentCoefficients
      {(algebraMap (Polynomial ℂ) RationalFunctions A)⁻¹} := by
    apply hspan
    rw [← hgen.2, unequalRankZetaValuesAt_rfl]
    exact mem_zetaSpan (unequalRankModel_mem_zetaValues qF ψ abv j k μ
      (rectangularMeasure νSD.val j (n + 1)) lambda ell f f' (han.1 f f') hR)
  obtain ⟨L, hL⟩ := Submodule.mem_span_singleton.mp hmem
  have hclear : laurentToRatFunc L = algebraMap (Polynomial ℂ) RationalFunctions A * R := by
    rw [← hL, Algebra.smul_def, algebraMap_laurent]
    rw [mul_left_comm, mul_inv_cancel₀ (RatFunc.algebraMap_ne_zero hA), mul_one]
  exact ⟨L, (TwoBlockFirstBlockLaurent.cleared_series_eq
    F.canonicalTopologicalData.residueCardinality_gt_one hclear hR ha).symm⟩

end Coefficients

section Blocks

variable {t r : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1) (htr : t < r)
  {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
  (ψ : UnitaryAdditiveCharacter F.Carrier)
  (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (π : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
  (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i))

/-- A real-ray clearing assertion for every actual nonzero-functional
coefficient in the opposite-twist family, with fixed block polynomials. -/
def StrictOppositeRealRayClearing
    (μ : Measure (LeftUnipotentQuotient t F.Carrier))
    (lambda : glFunctionals ψ r π) (P₀ P₁ : Polynomial ℂ) (C : ℝ) : Prop :=
  ∀ u : ℝ, C < u →
    ∀ ell : glInverseFunctionals ψ t (complexOppositeTwistInduced F m h σ (u : ℂ)),
      ell.val ≠ 0 →
    ∀ (j k : ℕ) (hr : r = t + (j + k + 1))
      (f : (coefficientModel π lambda).toSubmodule)
      (f' : (coefficientModel (complexOppositeTwistInduced F m h σ (u : ℂ)) ell).toSubmodule),
    let a : BilateralLaurentSeries :=
      strictSliceCoefficient F hr ψ μ ν.val f.val f'.val
    ∃ L : LaurentPolynomial ℂ, ofLaurentPolynomial L =
      oppositeSpectralClearingKernel qF P₀ P₁ (u : ℂ) • a

include htr in
/-- The large-twist symmetric bound, complete unramified transport and
uniqueness of normalized L polynomials give actual formal real-ray clearing. -/
theorem exists_strictOppositeRealRayClearing
    (hπ : IsOfWhittakerType r (standardCharacter ψ r) π)
    (hσ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i))
    [Measure.IsMulRightInvariant (unipotentHaar F.Carrier t)]
    (μ : Measure (LeftUnipotentQuotient t F.Carrier))
    (hμ : IsCompatible (upperUnipotent (t + 1) F.Carrier)
      (generalLinearHaar F.Carrier t) (unipotentHaar F.Carrier t) μ)
    (lambda : glFunctionals ψ r π) (hlambda : lambda.val ≠ 0)
    (P₀ P₁ : Polynomial ℂ)
    (hP₀ : IsPadicSymmetricLPolynomial F ψ ν.val π (σ 0) P₀)
    (hP₁ : IsPadicSymmetricLPolynomial F ψ ν.val π (σ 1) P₁) :
    ∃ C : ℝ, StrictOppositeRealRayClearing F h ψ ν π σ μ lambda P₀ P₁ C := by
  obtain ⟨Cbound, hC⟩ := exists_strictTwoBlockSymmetricLBound F h htr ψ ν π
    twoBlockDominantFirstBlockLaurentIdentity hπ σ hσ
  refine ⟨Cbound, fun u hu ell hell j k hr f f' => ?_⟩
  obtain ⟨P, Q₀, Q₁, hP, hQ₀, hQ₁, hdiv⟩ := hC u hu
  have hQ₀' := Padic.symmetricLPolynomial_determinantComplexPower
    F ψ ν π (σ 0) (-(u : ℂ)) P₀ hP₀
  have hQ₁' := Padic.symmetricLPolynomial_determinantComplexPower
    F ψ ν π (σ 1) (u : ℂ) P₁ hP₁
  have he0 : Q₀ = P₀.comp (C (spectralPoint qF (-(u : ℂ))) * X) := hQ₀.unique hQ₀'
  have he1 : Q₁ = P₁.comp (C (spectralPoint qF (u : ℂ)) * X) := hQ₁.unique hQ₁'
  rw [he0, he1] at hdiv
  let A := P₀.comp (C (spectralPoint qF (-(u : ℂ))) * X) *
    P₁.comp (C (spectralPoint qF (u : ℂ)) * X)
  have hA : A ≠ 0 := by
    have hc : A.coeff 0 = 1 := by
      simp [A, Polynomial.mul_coeff_zero, Polynomial.comp_C_mul_X_coeff,
        hP₀.coeff_zero, hP₁.coeff_zero]
    intro hz
    simp [hz] at hc
  exact strictRankCoefficient_clearing_of_certificate F hr ψ μ hμ π
    (complexOppositeTwistInduced F m h σ (u : ℂ)) hπ
    (complexOppositeTwistInduced_inverseWhittakerType F h ψ σ hσ (u : ℂ))
    lambda ell hlambda hell f f' ν P A hA hP hdiv

include htr in
/-- Continue the large-real-twist denominator bound to the original pair,
using actual entire determinant slices and the original ordered blocks. -/
theorem strictTwoBlockSymmetricLBound_at_zero
    (hπ : IsOfWhittakerType r (standardCharacter ψ r) π)
    (hσ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i)) :
    StrictTwoBlockSymmetricLBound F h ψ ν π σ := by
  let := unipotentHaar_isMulRightInvariant F.Carrier t
  let μ := unipotentQuotientHaar F.Carrier t
  have hμ := unipotentQuotientHaar_isCompatible F.Carrier t
  have hIndInv := lowerInduced_inverseWhittakerType F h ψ σ hσ
  have hInd := (isOfWhittakerType_standard_iff_inverse ψ _).mpr hIndInv
  obtain ⟨lambda, hlambda⟩ := hπ.exists_ne_zero
  obtain ⟨ell, hell⟩ := hIndInv.exists_ne_zero
  obtain ⟨P, hP⟩ := symmetricLPolynomialExists p F ψ ν r t V
    (TwoBlockJacquet.Sections F h σ) π (TwoBlockJacquet.inducedRep F h σ) hπ hInd
  obtain ⟨P₀, hP₀⟩ := symmetricLPolynomialExists p F ψ ν r (m 0) V
    (W 0) π (σ 0) hπ (hσ 0)
  obtain ⟨P₁, hP₁⟩ := symmetricLPolynomialExists p F ψ ν r (m 1) V
    (W 1) π (σ 1) hπ (hσ 1)
  obtain ⟨Cbound, hbound⟩ := exists_strictOppositeRealRayClearing F h htr ψ ν π σ
    hπ hσ μ hμ lambda hlambda P₀ P₁ hP₀ hP₁
  have hr0 : r = t + (0 + (r - t - 1) + 1) := by omega
  have hclear : ∀ (f : (coefficientModel π lambda).toSubmodule)
      (f' : (coefficientModel (TwoBlockJacquet.inducedRep F h σ) ell).toSubmodule),
      ∃ L : LaurentPolynomial ℂ, ofLaurentPolynomial L =
        (P₀ * P₁).toLaurent • strictSliceCoefficient F hr0 ψ μ ν.val f.val f'.val := by
    intro f f'
    obtain ⟨U, hU0, hcoeff, ⟨K, hKo, -, hK⟩, hUa⟩ :=
      exists_oppositeWhittakerFamily F m h σ ψ hσ ell hell f'
    have hae := strictSlices_entire F hr0 ψ μ ν.val π hπ lambda hlambda f U
      K hKo hK hUa
    let a : ℂ → BilateralLaurentSeries := fun u =>
      strictSliceCoefficient F hr0 ψ μ ν.val f.val (U u)
    have hreal : ∀ u : ℝ, Cbound < u → ∃ L : LaurentPolynomial ℂ,
        ofLaurentPolynomial L = oppositeSpectralClearingKernel qF P₀ P₁ (u : ℂ) •
          a (u : ℂ) := by
      intro u hu
      obtain ⟨ellU, hellU, v, hv⟩ := hcoeff (u : ℂ)
      have hfU : (modelMap _ ellU v).val = U (u : ℂ) := hv
      obtain ⟨L, hL⟩ := hbound u hu ellU hellU 0 (r - t - 1) hr0 f (modelMap _ ellU v)
      rw [hfU] at hL
      exact ⟨L, hL⟩
    obtain ⟨L, hL⟩ := oppositeSpectralKernel_laurent_clearing_at_zero
      F.canonicalTopologicalData.residueCardinality_gt_one P₀ P₁ a hae Cbound hreal
    exact ⟨L, by simpa only [a, hU0] using hL⟩
  have hA : P₀ * P₁ ≠ 0 := by
    have hc : (P₀ * P₁).coeff 0 = 1 := by
      rw [Polynomial.mul_coeff_zero, hP₀.coeff_zero, hP₁.coeff_zero, one_mul]
    intro hz
    simp [hz] at hc
  have hPμ := (isPairLPolynomial_of_lt htr).mp
    (((isPadicSymmetricLPolynomial_of_le htr.le).mp hP).2 μ hμ) 0 (r - t - 1) hr0
  exact ⟨P, P₀, P₁, hP, hP₀, hP₁,
    strictCoefficient_polynomialDivisibility F hr0 ψ μ ν.val π
      (TwoBlockJacquet.inducedRep F h σ) lambda ell hπ hIndInv hlambda hell
      P (P₀ * P₁) hA hPμ hclear⟩

end Blocks

end Langlands.RankinSelberg.DominantRankTransport
