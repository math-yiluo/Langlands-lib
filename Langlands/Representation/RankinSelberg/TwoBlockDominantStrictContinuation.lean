import Langlands.Representation.RankinSelberg.TwoBlockDominantStrictCoefficients
import Langlands.Representation.RankinSelberg.TwoBlockDominantCoefficientContinuation
import Langlands.Representation.RankinSelberg.UnequalRankAnalyticExtraction
import Langlands.Representation.RankinSelberg.UnequalRankAnalyticProof

noncomputable section

namespace Langlands.RankinSelberg.DominantRankTransport

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration
open HarmonicAnalysis.BilateralLaurentSeries

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance strictContinuationTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance strictContinuationValuation : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance strictContinuationLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance strictContinuationT2 : T2Space F.Carrier :=
  F.canonicalTopologicalData.fieldT2
local instance strictContinuationSecondCountable : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance strictContinuationSigmaCompact : SigmaCompactSpace F.Carrier :=
  F.canonicalTopologicalData.sigmaCompactSpace
local instance strictContinuationMeasurable : MeasurableSpace F.Carrier := borel _
local instance strictContinuationBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance strictContinuationGLMeasurable (n : ℕ) :
    MeasurableSpace (GeneralLinear (n + 1) F.Carrier) := borel _
local instance strictContinuationGLBorel (n : ℕ) :
    BorelSpace (GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
local instance strictContinuationUnipotentMeasurable (n : ℕ) :
    MeasurableSpace (upperUnipotent (n + 1) F.Carrier) := borel _
local instance strictContinuationUnipotentBorel (n : ℕ) :
    BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
local instance strictContinuationQuotientMeasurable (n : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient n F.Carrier) := borel _
local instance strictContinuationQuotientBorel (n : ℕ) :
    BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩

private theorem property_measurableSpace_transport {X : Type*}
    {m₁ m₂ : MeasurableSpace X} (hm : m₁ = m₂)
    (μ : @Measure X m₁)
    (P : (m : MeasurableSpace X) → @Measure X m → Prop)
    (hP : P m₁ μ) : P m₂ (hm ▸ μ) := by
  cases hm
  exact hP

private theorem integral_measurableSpace_transport {X : Type*}
    {m₁ m₂ : MeasurableSpace X} (hm : m₁ = m₂)
    (μ : @Measure X m₁) (φ : X → ℂ) :
    (letI := m₂; ∫ x, φ x ∂(hm ▸ μ)) =
      (letI := m₁; ∫ x, φ x ∂μ) := by
  cases hm
  rfl

/-- The supplied rectangle product remains sigma-finite under the canonical
Borel measurable-space identification. -/
instance strictRectangleMeasure_sigmaFinite (ν : AdditiveHaarMeasure F.Carrier)
    (j n : ℕ) : SigmaFinite (strictRectangleMeasure F ν j n) := by
  exact property_measurableSpace_transport _ (rectangularMeasure ν j n)
    (fun m μ => @SigmaFinite _ m μ) inferInstance

local notation "qF" => F.canonicalTopologicalData.residueCardinality
local notation "abv" => normalizedAbsoluteValue F.canonicalTopologicalData

variable {n r j k : ℕ}
  (hr : r = n + (j + k + 1))
  (ψ : UnitaryAdditiveCharacter F.Carrier)
  (μ : Measure (LeftUnipotentQuotient n F.Carrier))
  (ν : AdditiveHaarMeasure F.Carrier)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  (π : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
  (σ : Representation ℂ (GeneralLinear (n + 1) F.Carrier) W)
  (lambda : glFunctionals ψ r π) (ell : glInverseFunctionals ψ n σ)

/-- Published unequal-rank analysis for the exact supplied Haar rectangle,
transporting only its measurable-space presentation. -/
theorem strictRankAnalyticAt
    [Measure.IsMulRightInvariant (unipotentHaar F.Carrier n)]
    (hμ : IsCompatible (upperUnipotent (n + 1) F.Carrier)
      (generalLinearHaar F.Carrier n) (unipotentHaar F.Carrier n) μ)
    (hπ : IsOfWhittakerType r (standardCharacter ψ r) π)
    (hσ : IsOfWhittakerType n (inverseStandardCharacter ψ n) σ)
    (hlambda : lambda.val ≠ 0) (hell : ell.val ≠ 0) :
    letI := borel (Matrix (Fin j) (Fin (n + 1)) F.Carrier)
    UnequalRankAnalyticAt j k hr qF ψ abv μ
      (strictRectangleMeasure F ν j (n + 1)) π σ lambda ell := by
  subst r
  have hA := unequalRankAnalytic F F.canonicalTopologicalData n j k ψ μ hμ ν
    V W π σ hπ hσ lambda ell hlambda hell
  exact property_measurableSpace_transport _ (rectangularMeasure ν j (n + 1))
    (fun m νR => letI := m
      UnequalRankAnalyticAt j k rfl qF ψ abv μ νR π σ lambda ell) hA

/-- The fixed-rank Borel rectangle integral is exactly the original supplied
product-Haar integral. -/
theorem strictIntegral_eq
    (U : WhittakerFunctions ψ r) (U' : InverseWhittakerFunctions ψ n) :
    (letI := borel (Matrix (Fin j) (Fin (n + 1)) F.Carrier);
      unequalRankIntegral ψ abv j k μ (strictRectangleMeasure F ν j (n + 1))
        (hr ▸ U) U') =
      unequalRankIntegralAt j k hr ψ abv μ (rectangularMeasure ν j (n + 1)) U U' := by
  subst r
  funext s
  apply integral_congr_ae
  filter_upwards [] with z
  exact integral_measurableSpace_transport _ _ _

/-- The actual strict coefficients expand the original supplied-Haar integral
on a right half-plane; the same integral has a rational continuation. -/
theorem strictCoefficient_continuationData
    [Measure.IsMulRightInvariant (unipotentHaar F.Carrier n)]
    (hμ : IsCompatible (upperUnipotent (n + 1) F.Carrier)
      (generalLinearHaar F.Carrier n) (unipotentHaar F.Carrier n) μ)
    (hπ : IsOfWhittakerType r (standardCharacter ψ r) π)
    (hσ : IsOfWhittakerType n (inverseStandardCharacter ψ n) σ)
    (hlambda : lambda.val ≠ 0) (hell : ell.val ≠ 0)
    (f : (coefficientModel π lambda).toSubmodule)
    (f' : (coefficientModel σ ell).toSubmodule) :
    HasBilateralSpectralExpansion qF (strictSliceCoefficient F hr ψ μ ν f.val f'.val)
      (unequalRankIntegralAt j k hr ψ abv μ (rectangularMeasure ν j (n + 1))
        f.val f'.val) ∧
    ∃ R : RationalFunctions, HasRationalContinuation qF
      (unequalRankIntegralAt j k hr ψ abv μ (rectangularMeasure ν j (n + 1))
        f.val f'.val) R := by
  have hA := strictRankAnalyticAt F hr ψ μ ν π σ lambda ell hμ hπ hσ hlambda hell
  subst r
  have hI := strictIntegral_eq F rfl ψ μ ν f.val f'.val
  obtain ⟨R, hR⟩ := hA.2.1 f f'
  refine ⟨?_, R, ?_⟩
  · rw [← hI]
    exact unequalRank_hasBilateralSpectralExpansion F ψ μ j k
      (strictRectangleMeasure F ν j (n + 1)) f.val f'.val (hA.1 f f')
  · change HasRationalContinuation qF
      (letI := borel (Matrix (Fin j) (Fin (n + 1)) F.Carrier);
        unequalRankIntegral ψ abv j k μ (strictRectangleMeasure F ν j (n + 1))
          f.val f'.val) R at hR
    rwa [hI] at hR

/-- Uniform clearing of the actual fixed-rank coefficients controls the
intrinsic normalized generator for the original supplied product measure. -/
theorem strictCoefficient_polynomialDivisibility
    (hπ : IsOfWhittakerType r (standardCharacter ψ r) π)
    (hσ : IsOfWhittakerType n (inverseStandardCharacter ψ n) σ)
    (hlambda : lambda.val ≠ 0) (hell : ell.val ≠ 0)
    (P A : Polynomial ℂ) (hA : A ≠ 0)
    (hP : IsNormalizedGenerator
      (unequalRankZetaValuesAt j k hr qF ψ abv μ
        (rectangularMeasure ν j (n + 1)) π σ) P)
    (hclear : ∀ (f : (coefficientModel π lambda).toSubmodule)
      (f' : (coefficientModel σ ell).toSubmodule),
      ∃ N : LaurentPolynomial ℂ,
        ofLaurentPolynomial N =
          A.toLaurent • strictSliceCoefficient F hr ψ μ ν f.val f'.val) :
    ∃ (Q : Polynomial ℂ) (e : ℕ), Polynomial.X ^ e * A = Q * P := by
  subst r
  have hPBorel :
      letI := borel (Matrix (Fin j) (Fin (n + 1)) F.Carrier)
      IsUnequalRankLPolynomial qF ψ abv j k μ
        (strictRectangleMeasure F ν j (n + 1)) π σ P :=
    property_measurableSpace_transport _ (rectangularMeasure ν j (n + 1))
      (fun m νR => letI := m
        IsUnequalRankLPolynomial qF ψ abv j k μ νR π σ P) hP
  exact strictModelFiniteClearing_polynomialDivisibility F ψ μ j k
    (strictRectangleMeasure F ν j (n + 1)) π σ lambda ell
    hπ hσ hlambda hell P A hA hPBorel hclear

end Langlands.RankinSelberg.DominantRankTransport
