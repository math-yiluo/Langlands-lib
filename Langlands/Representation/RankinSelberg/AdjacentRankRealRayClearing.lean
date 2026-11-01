import Langlands.Representation.RankinSelberg.AdjacentRankSecondBlockCorankSpecialization
import Langlands.Representation.RankinSelberg.AdjacentRankImageLDivisibility
import Langlands.Representation.RankinSelberg.TwoBlockDominantJacquetSeries
import Langlands.Representation.RankinSelberg.WhittakerTypeTwist
import Langlands.Representation.RankinSelberg.TwoBlockSmallFunctionalEquationLaurentBridge

/-! Actual denominator bounds yield formal corank clearing through spectral uniqueness. -/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration
open scoped BigOperators

namespace Padic

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance realRayClearingTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance realRayClearingValuation : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance realRayClearingLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance realRayClearingFieldMeasurable : MeasurableSpace F.Carrier := borel _
local instance realRayClearingFieldBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance realRayClearingGroupMeasurable (r : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (r + 1) F.Carrier) := borel _
local instance realRayClearingGroupBorel (r : ℕ) :
    BorelSpace (Langlands.GeneralLinear (r + 1) F.Carrier) := ⟨rfl⟩
local instance realRayClearingUnipotentMeasurable (r : ℕ) :
    MeasurableSpace (upperUnipotent (r + 1) F.Carrier) := borel _
local instance realRayClearingUnipotentBorel (r : ℕ) :
    BorelSpace (upperUnipotent (r + 1) F.Carrier) := ⟨rfl⟩
local instance realRayClearingQuotientMeasurable (r : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient r F.Carrier) := borel _
local instance realRayClearingQuotientBorel (r : ℕ) :
    BorelSpace (LeftUnipotentQuotient r F.Carrier) := ⟨rfl⟩

local notation "T" => F.canonicalTopologicalData
local notation "abv" => normalizedAbsoluteValue T

/-- The rational reciprocal bound on the real ray, for every actual
nonzero-functional coefficient of the second deformed lower induction. -/
def SecondBlockCorankRealRayDenominatorBound
    {r : ℕ} (ψ : UnitaryAdditiveCharacter F.Carrier)
    (m : Fin 2 → ℕ) (h : ∑ i, (m i + 1) = (r + 1) + 1)
    {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (σ : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F.Carrier) (W i))
    (ν : Measure (LeftUnipotentQuotient r F.Carrier))
    (Wprime : InverseWhittakerFunctions ψ r)
    (P₀ P₁ : Polynomial ℂ) (C : ℝ) : Prop :=
  ∀ u : ℝ, C < u →
    ∀ ℓ : glFunctionals ψ (r + 1)
      (twoBlockSecondDeformedInduced F m h σ (u : ℂ)), ℓ.val ≠ 0 →
    ∀ v, AdjacentRankCorankDenominatorBound F ψ ν
      (coefficientMap (twoBlockSecondDeformedInduced F m h σ (u : ℂ)) ℓ v) Wprime
      (P₀ * P₁.comp (Polynomial.C
        (spectralPoint F.canonicalTopologicalData.residueCardinality (u : ℂ)) * Polynomial.X))

/-- Actual rational denominator membership clears the actual corank coefficients,
using scalar spectral uniqueness and the published full-type convergence. -/
theorem corankOneCoefficient_denominatorBound_clearing
    (hunique : BilateralSpectralCoefficientUniquenessStatement)
    (ψ : UnitaryAdditiveCharacter F.Carrier) {r : ℕ}
    [Measure.IsMulRightInvariant (unipotentHaar F.Carrier r)]
    (ν : Measure (LeftUnipotentQuotient r F.Carrier))
    (hν : IsCompatible (upperUnipotent (r + 1) F.Carrier)
      (generalLinearHaar F.Carrier r) (unipotentHaar F.Carrier r) ν)
    (μ : AdditiveHaarMeasure F.Carrier)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear ((r + 1) + 1) F.Carrier) V)
    (τ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) W)
    (hπ : IsOfWhittakerType (r + 1) (standardCharacter ψ (r + 1)) π)
    (hτ : IsOfWhittakerType r (inverseStandardCharacter ψ r) τ)
    (ℓU : glFunctionals ψ (r + 1) π) (hℓU : ℓU.val ≠ 0)
    (ℓprime : glInverseFunctionals ψ r τ) (hℓprime : ℓprime.val ≠ 0)
    (U : (coefficientModel π ℓU).toSubmodule)
    (Wprime : (coefficientModel τ ℓprime).toSubmodule)
    (P : Polynomial ℂ) (hP : P ≠ 0)
    (hbound : AdjacentRankCorankDenominatorBound F ψ ν U.val Wprime.val P) :
    ∃ L : LaurentPolynomial ℂ,
      BilateralLaurentSeries.ofLaurentPolynomial L = P.toLaurent •
        corankCoefficientSeries F ψ ν U.val Wprime.val := by
  have hA := unequalRankAnalytic F T r 0 0 ψ ν hν μ
    V W π τ hπ hτ ℓU ℓprime hℓU hℓprime
  obtain ⟨R, hR0⟩ := hA.2.1 U Wprime
  have hR : HasRationalContinuation F.canonicalTopologicalData.residueCardinality
      (fun s => corankOneIntegral ψ abv ν U.val Wprime.val s) R :=
    RationalContinuationLinear.continuation_of_eq_on_right hR0
      ⟨0, fun s _ => corankOneIntegral_eq_zeroZero F ψ ν μ U.val Wprime.val s⟩
  obtain ⟨L, hL⟩ := Submodule.mem_span_singleton.mp (hbound R hR)
  have hclear : laurentToRatFunc L = algebraMap (Polynomial ℂ) RationalFunctions P * R := by
    rw [← hL, Algebra.smul_def, algebraMap_laurent]
    rw [mul_left_comm, mul_inv_cancel₀ (RatFunc.algebraMap_ne_zero hP), mul_one]
  obtain ⟨C, hC⟩ := corankOneCoefficient_convergesOnRight F ψ ν hν μ π τ hπ hτ
    ℓU ℓprime hℓU hℓprime U Wprime
  refine ⟨L, (TwoBlockFirstBlockLaurent.cleared_series_eq_of_spectral_uniqueness
    hunique F.canonicalTopologicalData.residueCardinality_gt_one hclear hR ?_).symm⟩
  exact ⟨C, fun s hs => corankOneSliceExpansion F ψ U.val Wprime.val ν s (hC s hs)⟩

/-- The actual second-block lower induction has full standard type at every
complex parameter; all induced-type premises are discharged. -/
theorem secondBlockDeformed_isOfWhittakerType
    (ψ : UnitaryAdditiveCharacter F.Carrier) {t : ℕ}
    (m : Fin 2 → ℕ) (h : ∑ i, (m i + 1) = t + 1)
    {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (σ : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F.Carrier) (W i))
    (hσ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i))
    (u : ℂ) :
    IsOfWhittakerType t (standardCharacter ψ t)
      (twoBlockSecondDeformedInduced F m h σ u) := by
  have hu : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i))
      (twoBlockSecondDeformedBlocks F m σ u i) := by
    intro i
    exact (isOfWhittakerType_twist_iff _ _ (σ i)
      (F.canonicalTopologicalData.isOpen_ker_determinantComplexPower (m i + 1) _)
      (determinantComplexPower_upperUnipotent F (m i + 1) _)).mpr (hσ i)
  exact (isOfWhittakerType_standard_iff_inverse ψ _).mpr
    (DominantRankTransport.lowerInduced_inverseWhittakerType F h ψ
      (twoBlockSecondDeformedBlocks F m σ u) hu)

/-- Rational real-ray bounds for the actual family give the formal real-ray
clearing needed by entire coefficient specialization. -/
theorem secondBlock_realRayClearing_of_denominatorBound
    (hunique : BilateralSpectralCoefficientUniquenessStatement)
    (ψ : UnitaryAdditiveCharacter F.Carrier) {r : ℕ}
    [Measure.IsMulRightInvariant (unipotentHaar F.Carrier r)]
    (m : Fin 2 → ℕ) (h : ∑ i, (m i + 1) = (r + 1) + 1)
    {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (σ : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F.Carrier) (W i))
    (hσ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i))
    (ν : Measure (LeftUnipotentQuotient r F.Carrier))
    (hν : IsCompatible (upperUnipotent (r + 1) F.Carrier)
      (generalLinearHaar F.Carrier r) (unipotentHaar F.Carrier r) ν)
    (μ : AdditiveHaarMeasure F.Carrier)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (hτ : IsOfWhittakerType r (inverseStandardCharacter ψ r) τ)
    (ℓprime : glInverseFunctionals ψ r τ) (hℓprime : ℓprime.val ≠ 0)
    (Wprime : (coefficientModel τ ℓprime).toSubmodule)
    (P₀ P₁ : Polynomial ℂ) (hP₀ : P₀.coeff 0 = 1) (hP₁ : P₁.coeff 0 = 1)
    (C : ℝ)
    (hbound : SecondBlockCorankRealRayDenominatorBound F ψ m h σ ν Wprime.val P₀ P₁ C) :
    SecondBlockCorankRealRayClearing F ψ m h σ ν Wprime.val P₀ P₁ C := by
  intro u hu ℓ hℓ v
  let P := P₀ * P₁.comp (Polynomial.C
    (spectralPoint F.canonicalTopologicalData.residueCardinality (u : ℂ)) * Polynomial.X)
  have hP : P ≠ 0 := by
    have hconst : P.coeff 0 = 1 := by
      simp [P, Polynomial.mul_coeff_zero, Polynomial.comp_C_mul_X_coeff,
        hP₀, hP₁]
    intro hz
    simp [hz] at hconst
  exact corankOneCoefficient_denominatorBound_clearing F hunique ψ ν hν μ
    (twoBlockSecondDeformedInduced F m h σ (u : ℂ)) τ
    (secondBlockDeformed_isOfWhittakerType F ψ m h σ hσ (u : ℂ)) hτ
    ℓ hℓ ℓprime hℓprime (modelMap _ ℓ v) Wprime P hP (hbound u hu ℓ hℓ v)

end Padic
end Langlands.RankinSelberg
