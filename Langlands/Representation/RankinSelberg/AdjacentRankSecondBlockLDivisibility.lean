import Langlands.Representation.RankinSelberg.AdjacentRankSecondBlockCorankSpecialization
import Langlands.Representation.RankinSelberg.AdjacentRankClearedContinuation
import Langlands.Representation.RankinSelberg.AdjacentRankImageLDivisibility
import Langlands.Representation.RankinSelberg.TwoBlockDominantJacquetSeries

/-! Formal second-block clearing gives the original corank L-divisibility. -/

noncomputable section

namespace Langlands.RankinSelberg.Padic

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration
open scoped BigOperators

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance secondBlockLTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance secondBlockLValuation : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance secondBlockLLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance secondBlockLFieldMeasurable : MeasurableSpace F.Carrier := borel _
local instance secondBlockLFieldBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance secondBlockLGroupMeasurable (r : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (r + 1) F.Carrier) := borel _
local instance secondBlockLGroupBorel (r : ℕ) :
    BorelSpace (Langlands.GeneralLinear (r + 1) F.Carrier) := ⟨rfl⟩
local instance secondBlockLUnipotentMeasurable (r : ℕ) :
    MeasurableSpace (upperUnipotent (r + 1) F.Carrier) := borel _
local instance secondBlockLUnipotentBorel (r : ℕ) :
    BorelSpace (upperUnipotent (r + 1) F.Carrier) := ⟨rfl⟩
local instance secondBlockLQuotientMeasurable (r : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient r F.Carrier) := borel _
local instance secondBlockLQuotientBorel (r : ℕ) :
    BorelSpace (LeftUnipotentQuotient r F.Carrier) := ⟨rfl⟩

section Family

variable {t : ℕ} (m : Fin 2 → ℕ) (h : ∑ i, (m i + 1) = t + 1)
  {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
  (σ : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F.Carrier) (W i))

/-- An actual equivalence, including the section carriers, at parameter zero. -/
def secondBlockZeroEquiv :
    (twoBlockSecondDeformedInduced F m h σ 0).Equiv
      (TwoBlockJacquet.inducedRep F h σ) := by
  haveI := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
  exact Induction.smoothInducedEquiv ((succBlockShape m h).oppositeParabolic F.Carrier)
    (Representation.Equiv.mk (LinearEquiv.refl ℂ _) (fun q => by
      apply LinearMap.ext
      intro x
      change (F.canonicalTopologicalData.oppositeParabolicHalfModulus (succBlockShape m h) q :
            ℂ) •
          (succBlockShape m h).blockTensor (twoBlockSecondDeformedBlocks F m σ 0)
            ((succBlockShape m h).oppositeLeviProjection F.Carrier q) x =
        (F.canonicalTopologicalData.oppositeParabolicHalfModulus (succBlockShape m h) q :
            ℂ) •
          (succBlockShape m h).blockTensor σ
            ((succBlockShape m h).oppositeLeviProjection F.Carrier q) x
      rw [twoBlockSecondDeformedBlocks_zero]))

/-- Full standard type at zero follows from published complete block reversal
and full normalized upper type; no induced-type premise is added. -/
theorem secondBlockZero_isOfWhittakerType
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (hσ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i)) :
    IsOfWhittakerType t (standardCharacter ψ t)
      (twoBlockSecondDeformedInduced F m h σ 0) := by
  have htype := (isOfWhittakerType_standard_iff_inverse ψ _).mpr
    (DominantRankTransport.lowerInduced_inverseWhittakerType F h ψ σ hσ)
  exact htype.of_equiv (secondBlockZeroEquiv F m h σ).symm

end Family

/-- Every original coefficient image has the reciprocal product bound once
each actual deformed coefficient has formal real-ray clearing. -/
theorem secondBlock_modelDenominatorBound_at_zero
    (hdeform : TwoBlockSecondWhittakerDeformationStatement.{uF,uW})
    (ψ : UnitaryAdditiveCharacter F.Carrier) (μ : AdditiveHaarMeasure F.Carrier)
    {r : ℕ} [Measure.IsMulRightInvariant (unipotentHaar F.Carrier r)]
    (m : Fin 2 → ℕ) (h : ∑ i, (m i + 1) = (r + 1) + 1)
    {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (σ : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F.Carrier) (W i))
    (hσ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i))
    (J : glFunctionals ψ (r + 1) (twoBlockSecondDeformedInduced F m h σ 0))
    (hJ : J.val ≠ 0)
    (ν : Measure (LeftUnipotentQuotient r F.Carrier))
    (hν : IsCompatible (upperUnipotent (r + 1) F.Carrier)
      (generalLinearHaar F.Carrier r) (unipotentHaar F.Carrier r) ν)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (hτ : IsOfWhittakerType r (standardCharacter (ψ.scale (-1)) r) τ)
    (ℓprime : glFunctionals (ψ.scale (-1)) r τ) (hℓprime : ℓprime.val ≠ 0)
    (P₀ P₁ : Polynomial ℂ) (hprod : P₀ * P₁ ≠ 0)
    (hreal : ∀ Wprime : (coefficientModel τ ℓprime).toSubmodule,
      ∃ C : ℝ, SecondBlockCorankRealRayClearing F ψ m h σ ν
        (InducedTailIntermediate.scaledStandardAsInverse ψ Wprime.val) P₀ P₁ C) :
    AdjacentRankModelCorankDenominatorBound F ψ ν
      (twoBlockSecondDeformedInduced F m h σ 0) J τ ℓprime (P₀ * P₁) := by
  have hzero := secondBlockZero_isOfWhittakerType F m h σ ψ hσ
  have hτinv : IsOfWhittakerType r (inverseStandardCharacter ψ r) τ := by
    simpa only [standardCharacter_scale_neg_one] using hτ
  let ℓinv := functionalsCongr (standardCharacter_scale_neg_one ψ r) ℓprime
  intro U Wprime
  obtain ⟨C, hC⟩ := hreal Wprime
  let WprimeInv := scaledStandardCoefficientAsInverse F ψ τ ℓprime Wprime
  have hclear := secondBlock_corankClearing_at_zero F hdeform ψ r m h σ hσ J hJ U
    ν hν τ hτinv ℓinv WprimeInv P₀ P₁ C hC
  exact corankOneCoefficient_clearing_denominatorBound F ψ ν hν μ
    (twoBlockSecondDeformedInduced F m h σ 0) τ hzero hτinv
    J hJ ℓinv hℓprime U WprimeInv (P₀ * P₁) hprod hclear

/-- The specialized formal clearing has exactly the required L-polynomial
direction for the actual zero-parameter induced representation. -/
theorem secondBlock_polynomialDivisibility_at_zero
    (hdeform : TwoBlockSecondWhittakerDeformationStatement.{uF,uW})
    (ψ : UnitaryAdditiveCharacter F.Carrier) (μ : AdditiveHaarMeasure F.Carrier)
    {r : ℕ} [Measure.IsMulRightInvariant (unipotentHaar F.Carrier r)]
    (m : Fin 2 → ℕ) (h : ∑ i, (m i + 1) = (r + 1) + 1)
    {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (σ : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F.Carrier) (W i))
    (hσ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i))
    (J : glFunctionals ψ (r + 1) (twoBlockSecondDeformedInduced F m h σ 0))
    (hJ : J.val ≠ 0)
    (ν : Measure (LeftUnipotentQuotient r F.Carrier))
    (hν : IsCompatible (upperUnipotent (r + 1) F.Carrier)
      (generalLinearHaar F.Carrier r) (unipotentHaar F.Carrier r) ν)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (hτ : IsOfWhittakerType r (standardCharacter (ψ.scale (-1)) r) τ)
    (ℓprime : glFunctionals (ψ.scale (-1)) r τ) (hℓprime : ℓprime.val ≠ 0)
    (P P₀ P₁ : Polynomial ℂ) (hprod : P₀ * P₁ ≠ 0)
    (hP : IsPadicSymmetricLPolynomial F ψ μ
      (twoBlockSecondDeformedInduced F m h σ 0) τ P)
    (hreal : ∀ Wprime : (coefficientModel τ ℓprime).toSubmodule,
      ∃ C : ℝ, SecondBlockCorankRealRayClearing F ψ m h σ ν
        (InducedTailIntermediate.scaledStandardAsInverse ψ Wprime.val) P₀ P₁ C) :
    ∃ (Q : Polynomial ℂ) (e : ℕ),
      Polynomial.X ^ e * (P₀ * P₁) = Q * P := by
  exact adjacentRankModelBound_polynomialDivisibility F ψ μ ν hν
    (twoBlockSecondDeformedInduced F m h σ 0)
    (secondBlockZero_isOfWhittakerType F m h σ ψ hσ) J hJ τ hτ ℓprime hℓprime
    P (P₀ * P₁) hprod hP
    (secondBlock_modelDenominatorBound_at_zero F hdeform ψ μ m h σ hσ J hJ
      ν hν τ hτ ℓprime hℓprime P₀ P₁ hprod hreal)

end Langlands.RankinSelberg.Padic
