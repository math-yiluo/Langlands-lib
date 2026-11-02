import Langlands.Representation.RankinSelberg.TwoBlockDominantEqualFactors
import Langlands.Representation.RankinSelberg.TwoBlockDominantEqualEntireSlices
import Langlands.Representation.RankinSelberg.TwoBlockDominantOppositeDeformation
import Langlands.Representation.RankinSelberg.TwoBlockDominantOppositeKernel
import Langlands.Representation.RankinSelberg.PadicPairLPolynomialNormalization
import Langlands.Representation.RankinSelberg.TwoBlockSmallFunctionalEquationLaurentBridge

noncomputable section

namespace Langlands.RankinSelberg.DominantRankTransport

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration
  Polynomial TwoBlockLowerUnipotentQuotient

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance equalLContinuationTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance equalLContinuationValuation : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance equalLContinuationLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance equalLContinuationT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance equalLContinuationMeasurable : MeasurableSpace F.Carrier := borel _
local instance equalLContinuationBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance equalLContinuationGLMeasurable (n : ℕ) :
    MeasurableSpace (GeneralLinear (n + 1) F.Carrier) := borel _
local instance equalLContinuationGLBorel (n : ℕ) :
    BorelSpace (GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
local instance equalLContinuationUnipotentMeasurable (n : ℕ) :
    MeasurableSpace (upperUnipotent (n + 1) F.Carrier) := borel _
local instance equalLContinuationUnipotentBorel (n : ℕ) :
    BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
local instance equalLContinuationQuotientMeasurable (n : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient n F.Carrier) := borel _
local instance equalLContinuationQuotientBorel (n : ℕ) :
    BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩

local notation "qF" => F.canonicalTopologicalData.residueCardinality
local notation "abv" => normalizedAbsoluteValue F.canonicalTopologicalData

open ParameterSpecialization HarmonicAnalysis.BilateralLaurentSeries
open AdjacentGammaContinuation

section Coefficients

variable {n : ℕ} (ψ : UnitaryAdditiveCharacter F.Carrier)
  (μ : Measure (LeftUnipotentQuotient n F.Carrier))
  [Measure.IsMulRightInvariant (unipotentHaar F.Carrier n)]
  (hμ : IsCompatible (upperUnipotent (n + 1) F.Carrier)
    (generalLinearHaar F.Carrier n) (unipotentHaar F.Carrier n) μ)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {U : Type uW} [AddCommGroup U] [Module ℂ U]
  (π : Representation ℂ (GeneralLinear (n + 1) F.Carrier) V)
  (τ : Representation ℂ (GeneralLinear (n + 1) F.Carrier) U)
  (hπ : IsOfWhittakerType n (standardCharacter ψ n) π)
  (hτ : IsOfWhittakerType n (inverseStandardCharacter ψ n) τ)
  (lambda : glFunctionals ψ n π) (ell : glInverseFunctionals ψ n τ)
  (hlambda : lambda.val ≠ 0) (hell : ell.val ≠ 0)
  (f : (coefficientModel π lambda).toSubmodule)
  (f' : (coefficientModel τ ell).toSubmodule)
  (Φ : SchwartzBruhat (Fin (n + 1) → F.Carrier))

include hμ hπ hτ hlambda hell

/-- Full type supplies a rational continuation and an absolute expansion
of the same actual equal-rank integral. -/
theorem equalRankCoefficient_continuationData :
    ∃ R : RationalFunctions,
      HasRationalContinuation qF
        (fun s => equalRankIntegral ψ abv μ f.val f'.val Φ s) R ∧
      HasAbsoluteBilateralSpectralExpansion qF
        (equalRankSliceCoefficient F.canonicalTopologicalData μ ψ f.val f'.val Φ)
        (fun s => equalRankIntegral ψ abv μ f.val f'.val Φ s) := by
  have han := equalRankAnalytic F F.canonicalTopologicalData n ψ μ hμ
    V U π τ hπ hτ lambda ell hlambda hell
  obtain ⟨R, hR⟩ := han.2.1 f f' Φ
  obtain ⟨C, hC⟩ := han.1 f f' Φ
  exact ⟨R, hR, C, fun s hs =>
    (equalRankSliceExpansion F F.canonicalTopologicalData n μ ψ f.val f'.val Φ s
      (hC s hs)).2⟩

/-- A complete L certificate and its polynomial divisibility clear each
actual equal-rank coefficient vector, by scalar spectral uniqueness. -/
theorem equalRankCoefficient_clearing_of_certificate
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    (P A : Polynomial ℂ) (hA : A ≠ 0)
    (hP : IsPadicSymmetricLPolynomial F ψ ν.val π τ P)
    (hdiv : ∃ (Q : Polynomial ℂ) (e : ℕ), X ^ e * A = Q * P) :
    let a : BilateralLaurentSeries :=
      equalRankSliceCoefficient F.canonicalTopologicalData μ ψ f.val f'.val Φ
    ∃ L : LaurentPolynomial ℂ, ofLaurentPolynomial L = A.toLaurent • a := by
  have hgen : IsNormalizedGenerator (equalRankZetaValues qF ψ abv μ π τ) P :=
    isPairLPolynomial_self.mp (((isPadicSymmetricLPolynomial_of_le (le_refl n)).mp hP).2 μ hμ)
  have hspan : Submodule.span LaurentCoefficients
      {(algebraMap (Polynomial ℂ) RationalFunctions P)⁻¹} ≤
      Submodule.span LaurentCoefficients
        {(algebraMap (Polynomial ℂ) RationalFunctions A)⁻¹} :=
    (Submodule.span_singleton_le_iff_mem _ _).mpr
      ((reciprocalLaurentSpanClearing P A hgen.polynomial_ne_zero hA).mpr hdiv)
  have han := equalRankAnalytic F F.canonicalTopologicalData n ψ μ hμ
    V U π τ hπ hτ lambda ell hlambda hell
  obtain ⟨R, hR, ha⟩ := equalRankCoefficient_continuationData F ψ μ hμ
    π τ hπ hτ lambda ell hlambda hell f f' Φ
  have hmem : R ∈ Submodule.span LaurentCoefficients
      {(algebraMap (Polynomial ℂ) RationalFunctions A)⁻¹} := by
    apply hspan
    rw [← hgen.2]
    exact mem_zetaSpan (equalRankModel_mem_zetaValues qF ψ abv μ
      lambda ell f f' Φ (han.1 f f' Φ) hR)
  obtain ⟨L, hL⟩ := Submodule.mem_span_singleton.mp hmem
  have hclear : laurentToRatFunc L = algebraMap (Polynomial ℂ) RationalFunctions A * R := by
    rw [← hL, Algebra.smul_def, algebraMap_laurent]
    rw [mul_left_comm, mul_inv_cancel₀ (RatFunc.algebraMap_ne_zero hA), mul_one]
  exact ⟨L, (TwoBlockFirstBlockLaurent.cleared_series_eq
    F.canonicalTopologicalData.residueCardinality_gt_one hclear hR ha).symm⟩

end Coefficients

section Blocks

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)
  {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
  (ψ : UnitaryAdditiveCharacter F.Carrier)
  (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (π : Representation ℂ (GeneralLinear (t + 1) F.Carrier) V)
  (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i))

/-- The actual opposite lower induction retains full inverse Whittaker type
at every complex parameter. -/
theorem complexOppositeTwistInduced_inverseWhittakerType
    (hσ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i))
    (u : ℂ) :
    IsOfWhittakerType t (inverseStandardCharacter ψ t)
      (complexOppositeTwistInduced F m h σ u) := by
  have hu : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i))
      (complexOppositeTwistBlocks F m σ u i) := by
    intro i
    exact (isOfWhittakerType_twist_iff _ _ (σ i)
      (F.canonicalTopologicalData.isOpen_ker_determinantComplexPower (m i + 1) _)
      (determinantComplexPower_upperUnipotent F (m i + 1) _)).mpr (hσ i)
  exact lowerInduced_inverseWhittakerType F h ψ (complexOppositeTwistBlocks F m σ u) hu

/-- A real-ray clearing assertion for every actual nonzero-functional
coefficient in the opposite-twist family, with fixed block polynomials. -/
def EqualOppositeRealRayClearing
    (μ : Measure (LeftUnipotentQuotient t F.Carrier))
    (lambda : glFunctionals ψ t π) (P₀ P₁ : Polynomial ℂ) (C : ℝ) : Prop :=
  ∀ u : ℝ, C < u →
    ∀ ell : glInverseFunctionals ψ t (complexOppositeTwistInduced F m h σ (u : ℂ)),
      ell.val ≠ 0 →
    ∀ (f : (coefficientModel π lambda).toSubmodule)
      (f' : (coefficientModel (complexOppositeTwistInduced F m h σ (u : ℂ)) ell).toSubmodule)
      (Φ : SchwartzBruhat (Fin (t + 1) → F.Carrier)),
    let a : BilateralLaurentSeries :=
      equalRankSliceCoefficient F.canonicalTopologicalData μ ψ f.val f'.val Φ
    ∃ L : LaurentPolynomial ℂ, ofLaurentPolynomial L =
      oppositeSpectralClearingKernel qF P₀ P₁ (u : ℂ) • a

/-- The large-twist symmetric bound, complete unramified transport and
uniqueness of normalized L polynomials give actual formal real-ray clearing. -/
theorem exists_equalOppositeRealRayClearing
    (hπ : IsOfWhittakerType t (standardCharacter ψ t) π)
    (hσ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i))
    [Measure.IsMulRightInvariant (unipotentHaar F.Carrier t)]
    (μ : Measure (LeftUnipotentQuotient t F.Carrier))
    (hμ : IsCompatible (upperUnipotent (t + 1) F.Carrier)
      (generalLinearHaar F.Carrier t) (unipotentHaar F.Carrier t) μ)
    (lambda : glFunctionals ψ t π) (hlambda : lambda.val ≠ 0)
    (P₀ P₁ : Polynomial ℂ)
    (hP₀ : IsPadicSymmetricLPolynomial F ψ ν.val π (σ 0) P₀)
    (hP₁ : IsPadicSymmetricLPolynomial F ψ ν.val π (σ 1) P₁) :
    ∃ C : ℝ, EqualOppositeRealRayClearing F h ψ π σ μ lambda P₀ P₁ C := by
  obtain ⟨Cbound, hC⟩ := exists_equalTwoBlockSymmetricLBound F h ψ ν π hπ σ hσ
  refine ⟨Cbound, fun u hu ell hell f f' Φ => ?_⟩
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
  exact equalRankCoefficient_clearing_of_certificate F ψ μ hμ π
    (complexOppositeTwistInduced F m h σ (u : ℂ)) hπ
    (complexOppositeTwistInduced_inverseWhittakerType F h ψ σ hσ (u : ℂ))
    lambda ell hlambda hell f f' Φ ν P A hA hP hdiv

/-- Continue the large-real-twist denominator bound to the original pair,
using actual entire determinant slices and the original ordered blocks. -/
theorem equalTwoBlockSymmetricLBound_at_zero
    (hπ : IsOfWhittakerType t (standardCharacter ψ t) π)
    (hσ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i)) :
    EqualTwoBlockSymmetricLBound F h ψ ν π σ := by
  let := unipotentHaar_isMulRightInvariant F.Carrier t
  let μ := unipotentQuotientHaar F.Carrier t
  have hμ := unipotentQuotientHaar_isCompatible F.Carrier t
  have hIndInv := lowerInduced_inverseWhittakerType F h ψ σ hσ
  have hInd := (isOfWhittakerType_standard_iff_inverse ψ _).mpr hIndInv
  obtain ⟨lambda, hlambda⟩ := hπ.exists_ne_zero
  obtain ⟨ell, hell⟩ := hIndInv.exists_ne_zero
  obtain ⟨P, hP⟩ := symmetricLPolynomialExists p F ψ ν t t V
    (TwoBlockJacquet.Sections F h σ) π (TwoBlockJacquet.inducedRep F h σ) hπ hInd
  obtain ⟨P₀, hP₀⟩ := symmetricLPolynomialExists p F ψ ν t (m 0) V
    (W 0) π (σ 0) hπ (hσ 0)
  obtain ⟨P₁, hP₁⟩ := symmetricLPolynomialExists p F ψ ν t (m 1) V
    (W 1) π (σ 1) hπ (hσ 1)
  obtain ⟨Cbound, hbound⟩ := exists_equalOppositeRealRayClearing F h ψ ν π σ
    hπ hσ μ hμ lambda hlambda P₀ P₁ hP₀ hP₁
  have hclear : EqualModelFiniteClearing F ψ μ π (TwoBlockJacquet.inducedRep F h σ)
      lambda ell (P₀ * P₁) := by
    intro f f' Φ
    obtain ⟨U, hU0, hcoeff, ⟨K, hKo, -, hK⟩, hUa⟩ :=
      exists_oppositeWhittakerFamily F m h σ ψ hσ ell hell f'
    have hae := (equalRankEntireSliceData F ψ μ π lambda f Φ U hπ.1.1
      K hKo hK hUa).2
    let a : ℂ → BilateralLaurentSeries := fun u =>
      equalRankSliceCoefficient F.canonicalTopologicalData μ ψ f.val (U u) Φ
    have hreal : ∀ u : ℝ, Cbound < u → ∃ L : LaurentPolynomial ℂ,
        ofLaurentPolynomial L = oppositeSpectralClearingKernel qF P₀ P₁ (u : ℂ) •
          a (u : ℂ) := by
      intro u hu
      obtain ⟨ellU, hellU, v, hv⟩ := hcoeff (u : ℂ)
      have hfU : (modelMap _ ellU v).val = U (u : ℂ) := hv
      obtain ⟨L, hL⟩ := hbound u hu ellU hellU f (modelMap _ ellU v) Φ
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
  have hPμ := isPairLPolynomial_self.mp
    (((isPadicSymmetricLPolynomial_of_le (le_refl t)).mp hP).2 μ hμ)
  exact ⟨P, P₀, P₁, hP, hP₀, hP₁,
    equalModelFiniteClearing_polynomialDivisibility F ψ μ π
      (TwoBlockJacquet.inducedRep F h σ) lambda ell hπ hIndInv hlambda hell
      P (P₀ * P₁) hA hPμ hclear⟩

end Blocks

end Langlands.RankinSelberg.DominantRankTransport
