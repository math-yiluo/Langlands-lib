import Langlands.Representation.RankinSelberg.AdjacentRankRealRayClearing
import Langlands.Representation.RankinSelberg.AdjacentRankLargeTwistLDivisibility
import Langlands.Representation.RankinSelberg.BilateralSpectralCoefficientUniquenessProof

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration
open scoped BigOperators

namespace Padic

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance certifiedRealRayTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance certifiedRealRayValuation : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance certifiedRealRayLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance certifiedRealRayFieldMeasurable : MeasurableSpace F.Carrier := borel _
local instance certifiedRealRayFieldBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance certifiedRealRayGroupMeasurable (r : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (r + 1) F.Carrier) := borel _
local instance certifiedRealRayGroupBorel (r : ℕ) :
    BorelSpace (Langlands.GeneralLinear (r + 1) F.Carrier) := ⟨rfl⟩
local instance certifiedRealRayUnipotentMeasurable (r : ℕ) :
    MeasurableSpace (upperUnipotent (r + 1) F.Carrier) := borel _
local instance certifiedRealRayUnipotentBorel (r : ℕ) :
    BorelSpace (upperUnipotent (r + 1) F.Carrier) := ⟨rfl⟩
local instance certifiedRealRayQuotientMeasurable (r : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient r F.Carrier) := borel _
local instance certifiedRealRayQuotientBorel (r : ℕ) :
    BorelSpace (LeftUnipotentQuotient r F.Carrier) := ⟨rfl⟩

local notation "T" => F.canonicalTopologicalData
local notation "abv" => normalizedAbsoluteValue T

/-- A complete induced L certificate and its exact polynomial divisibility
bound each actual corank coefficient, for the supplied compatible measure. -/
theorem corankOneCoefficient_denominatorBound_of_certificate
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
    (P A : Polynomial ℂ) (hA : A ≠ 0)
    (hP : IsPadicSymmetricLPolynomial F ψ μ π τ P)
    (hdiv : ∃ (Q : Polynomial ℂ) (e : ℕ), Polynomial.X ^ e * A = Q * P) :
    AdjacentRankCorankDenominatorBound F ψ ν U.val Wprime.val A := by
  have hPair : IsPairLPolynomial F.canonicalTopologicalData.residueCardinality
      ψ abv ν μ π τ P :=
    ((isPadicSymmetricLPolynomial_of_le (Nat.le_succ r)).mp hP).2 ν hν
  have hgen : IsNormalizedGenerator
      (unequalRankZetaValues F.canonicalTopologicalData.residueCardinality ψ abv
        0 0 ν (rectangularMeasure μ 0 (r + 1)) π τ) P :=
    (isPairLPolynomial_of_lt (Nat.lt_succ_self r)).mp hPair 0 0 rfl
  have hspan : Submodule.span LaurentCoefficients
      {(algebraMap (Polynomial ℂ) RationalFunctions P)⁻¹} ≤
      Submodule.span LaurentCoefficients
        {(algebraMap (Polynomial ℂ) RationalFunctions A)⁻¹} :=
    (Submodule.span_singleton_le_iff_mem _ _).mpr
      ((reciprocalLaurentSpanClearing P A hgen.polynomial_ne_zero hA).mpr hdiv)
  have hAconv := unequalRankAnalytic F T r 0 0 ψ ν hν μ
    V W π τ hπ hτ ℓU ℓprime hℓU hℓprime
  intro R hR
  apply hspan
  rw [← hgen.2]
  apply mem_zetaSpan
  apply unequalRankModel_mem_zetaValues
    F.canonicalTopologicalData.residueCardinality ψ abv 0 0 ν
      (rectangularMeasure μ 0 (r + 1)) ℓU ℓprime U Wprime
  · exact hAconv.1 U Wprime
  · exact RationalContinuationLinear.continuation_of_eq_on_right hR
      ⟨0, fun s _ => (corankOneIntegral_eq_zeroZero F ψ ν μ U.val Wprime.val s).symm⟩

/-- Complete induced certificates with the fixed rescaled block product on
one real ray. The certificates and polynomial relation remain explicit. -/
def SecondBlockCorankRealRayCertificates
    {r : ℕ} (ψ : UnitaryAdditiveCharacter F.Carrier)
    (μ : AdditiveHaarMeasure F.Carrier)
    (m : Fin 2 → ℕ) (h : ∑ i, (m i + 1) = (r + 1) + 1)
    {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (σ : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F.Carrier) (W i))
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (P₀ P₁ : Polynomial ℂ) (C : ℝ) : Prop :=
  ∀ u : ℝ, C < u → ∃ P : Polynomial ℂ,
    IsPadicSymmetricLPolynomial F ψ μ
      (twoBlockSecondDeformedInduced F m h σ (u : ℂ)) τ P ∧
    ∃ (Q : Polynomial ℂ) (e : ℕ),
      Polynomial.X ^ e * (P₀ * P₁.comp (Polynomial.C
        (spectralPoint F.canonicalTopologicalData.residueCardinality (u : ℂ)) *
          Polynomial.X)) = Q * P

/-- Complete certificates and exact polynomial divisibility supply the
actual reciprocal-span bound for every actual coefficient on the same ray. -/
theorem secondBlock_realRayDenominatorBound_of_certificates
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
    (hcert : SecondBlockCorankRealRayCertificates F ψ μ m h σ τ P₀ P₁ C) :
    SecondBlockCorankRealRayDenominatorBound F ψ m h σ ν Wprime.val P₀ P₁ C := by
  intro u hu ℓ hℓ v
  obtain ⟨P, hP, hdiv⟩ := hcert u hu
  let A := P₀ * P₁.comp (Polynomial.C
    (spectralPoint F.canonicalTopologicalData.residueCardinality (u : ℂ)) * Polynomial.X)
  have hA : A ≠ 0 := by
    have hconst : A.coeff 0 = 1 := by
      simp [A, Polynomial.mul_coeff_zero, Polynomial.comp_C_mul_X_coeff, hP₀, hP₁]
    intro hz
    simp [hz] at hconst
  exact corankOneCoefficient_denominatorBound_of_certificate F ψ ν hν μ
    (twoBlockSecondDeformedInduced F m h σ (u : ℂ)) τ
    (secondBlockDeformed_isOfWhittakerType F ψ m h σ hσ (u : ℂ)) hτ
    ℓ hℓ ℓprime hℓprime (modelMap _ ℓ v) Wprime P A hA hP hdiv

/-- Published scalar spectral uniqueness converts certified actual
real-ray polynomial divisibility to formal coefficient clearing. -/
theorem secondBlock_realRayClearing_of_certificates
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
    (hcert : SecondBlockCorankRealRayCertificates F ψ μ m h σ τ P₀ P₁ C) :
    SecondBlockCorankRealRayClearing F ψ m h σ ν Wprime.val P₀ P₁ C :=
  secondBlock_realRayClearing_of_denominatorBound F bilateralSpectralCoefficientUniqueness
    ψ m h σ hσ ν hν μ τ hτ ℓprime hℓprime Wprime P₀ P₁ hP₀ hP₁ C
    (secondBlock_realRayDenominatorBound_of_certificates F ψ m h σ hσ ν hν μ
      τ hτ ℓprime hℓprime Wprime P₀ P₁ hP₀ hP₁ C hcert)

end Padic
end Langlands.RankinSelberg
