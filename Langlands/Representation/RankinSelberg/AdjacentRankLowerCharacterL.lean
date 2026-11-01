import Langlands.Representation.RankinSelberg.AdjacentRankFixedPolynomials
import Langlands.Representation.RankinSelberg.AdjacentRankSecondBlockLDivisibility
import Langlands.Representation.RankinSelberg.TwoBlockSecondWhittakerDeformationProof

noncomputable section

namespace Langlands.RankinSelberg.Padic

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration
open scoped BigOperators

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance lowerCharacterLTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance lowerCharacterLValuation : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance lowerCharacterLLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance lowerCharacterLT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance lowerCharacterLTotallyDisconnected : TotallyDisconnectedSpace F.Carrier := by
  let : NonarchimedeanRing F.Carrier := by
    convert! ValuativeRel.nonarchimedeanRing F.Carrier
    exact Valuation.toTopologicalSpace_eq _
  infer_instance
local instance lowerCharacterLFieldMeasurable : MeasurableSpace F.Carrier := borel _
local instance lowerCharacterLFieldBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance lowerCharacterLGroupMeasurable (r : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (r + 1) F.Carrier) := borel _
local instance lowerCharacterLGroupBorel (r : ℕ) :
    BorelSpace (Langlands.GeneralLinear (r + 1) F.Carrier) := ⟨rfl⟩
local instance lowerCharacterLUnipotentMeasurable (r : ℕ) :
    MeasurableSpace (upperUnipotent (r + 1) F.Carrier) := borel _
local instance lowerCharacterLUnipotentBorel (r : ℕ) :
    BorelSpace (upperUnipotent (r + 1) F.Carrier) := ⟨rfl⟩
local instance lowerCharacterLQuotientMeasurable (r : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient r F.Carrier) := borel _
local instance lowerCharacterLQuotientBorel (r : ℕ) :
    BorelSpace (LeftUnipotentQuotient r F.Carrier) := ⟨rfl⟩


private theorem lowerCharacterL_certificate_coeff_zero
    (ψ : UnitaryAdditiveCharacter F.Carrier) (μ : AdditiveHaarMeasure F.Carrier)
    {r n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (τ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
    (P : Polynomial ℂ) (hP : IsPadicSymmetricLPolynomial F ψ μ π τ P) :
    P.coeff 0 = 1 := by
  unfold IsPadicSymmetricLPolynomial at hP
  split_ifs at hP
  · obtain ⟨⟨hinv, ν, hν⟩, hall⟩ := hP
    let := hinv
    exact (hall ν hν).coeff_zero
  · obtain ⟨⟨hinv, ν, hν⟩, hall⟩ := hP
    let := hinv
    exact (hall ν hν).coeff_zero

/-- Complete certificates and product divisibility for every character in the
actual ordered lower adjacent-rank pair. -/
def AdjacentRankLowerCharacterL
    (ψ : UnitaryAdditiveCharacter F.Carrier) (μ : AdditiveHaarMeasure F.Carrier)
    {r : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (τ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) W)
    (χ : Quasicharacter F.Carrier) : Prop :=
  let B := Shahidi.twoBlocks (r + 1) 1 (Nat.succ_pos r) (Nat.succ_pos 0)
  let ρ := F.canonicalNormalizedOppositeParabolicInduced B
    (B.blockTensor (Shahidi.pairFamily σ (rankOneExtensionCharacter.{uF,uV} F χ)))
  ∃ P P₀ P₁ : Polynomial ℂ,
    IsPadicSymmetricLPolynomial F ψ μ τ ρ P ∧
    IsPadicSymmetricLPolynomial F ψ μ τ σ P₀ ∧
    IsPadicSymmetricLPolynomial F ψ μ τ (rankOneExtensionCharacter.{uF,uV} F χ) P₁ ∧
    ∃ (Q : Polynomial ℂ) (e : ℕ), Polynomial.X ^ e * (P₀ * P₁) = Q * P

/-- Specialize the actual certified second-block deformation at zero. -/
theorem adjacentRankLowerCharacterL
    (ψ : UnitaryAdditiveCharacter F.Carrier) (μ : AdditiveHaarMeasure F.Carrier)
    (hself : IsSelfDual ψ μ) {r : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (τ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) W)
    (hσ : IsOfWhittakerType r (standardCharacter ψ r) σ)
    (hτ : IsOfWhittakerType r (standardCharacter ψ r) τ)
    (χ : Quasicharacter F.Carrier) :
    AdjacentRankLowerCharacterL F ψ μ σ τ χ := by
  let m : Fin 2 → ℕ := ![r, 0]
  let h : ∑ i, (m i + 1) = (r + 1) + 1 := adjacentLowerPair_sum r
  let β := adjacentLowerPairBlocks F σ χ
  have hβ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (β i) := by
    intro i
    fin_cases i
    · exact hσ
    · exact rankOneExtensionCharacter_isOfWhittakerType F ψ χ
  obtain ⟨P₀, P₁, C, hP₀, hP₁, hcert⟩ :=
    adjacentLowerPair_fixedRealRayCertificates F ψ μ hself σ τ hσ hτ χ
  have hc₀ := lowerCharacterL_certificate_coeff_zero F ψ μ τ σ P₀ hP₀
  have hc₁ := lowerCharacterL_certificate_coeff_zero F ψ μ τ
    (rankOneExtensionCharacter.{uF,uV} F χ) P₁ hP₁
  have hprod : P₀ * P₁ ≠ 0 := by
    intro hz
    have hc : (P₀ * P₁).coeff 0 = 1 := by
      simp only [Polynomial.mul_coeff_zero, hc₀, hc₁, one_mul]
    simp only [hz, Polynomial.coeff_zero, zero_ne_one] at hc
  let ρ₀ := twoBlockSecondDeformedInduced F m h β 0
  have hρ₀ : IsOfWhittakerType (r + 1) (standardCharacter ψ (r + 1)) ρ₀ :=
    secondBlockZero_isOfWhittakerType F m h β ψ hβ
  obtain ⟨J, hJ⟩ := hρ₀.exists_ne_zero
  have hτs : IsOfWhittakerType r (standardCharacter (ψ.scale (-1)) r) τ := by
    simpa only [standardCharacter_scale_neg_one] using
      (isOfWhittakerType_standard_iff_inverse ψ τ).mp hτ
  obtain ⟨ℓprime, hℓprime⟩ := hτs.exists_ne_zero
  let μsd : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ := ⟨μ, hself⟩
  obtain ⟨P, hP⟩ := symmetricLPolynomialExists p F ψ μsd (r + 1) r _ W ρ₀ τ hρ₀ hτ
  have hPair : IsPadicPairLPolynomial F ψ μ ρ₀ τ P :=
    (isPadicSymmetricLPolynomial_of_le (Nat.le_succ r)).mp hP
  obtain ⟨⟨hinv, ν, hν⟩, -⟩ := hPair
  let := hinv
  have hτinv : IsOfWhittakerType r (inverseStandardCharacter ψ r) τ :=
    (isOfWhittakerType_standard_iff_inverse ψ τ).mp hτ
  let ℓinv := functionalsCongr (standardCharacter_scale_neg_one ψ r) ℓprime
  have hreal : ∀ Wprime : (coefficientModel τ ℓprime).toSubmodule,
      ∃ C : ℝ, SecondBlockCorankRealRayClearing F ψ m h β ν
        (InducedTailIntermediate.scaledStandardAsInverse ψ Wprime.val) P₀ P₁ C := by
    intro Wprime
    exact ⟨C, secondBlock_realRayClearing_of_certificates F ψ m h β hβ ν hν μ
      τ hτinv ℓinv hℓprime (scaledStandardCoefficientAsInverse F ψ τ ℓprime Wprime)
      P₀ P₁ hc₀ hc₁ C hcert⟩
  obtain ⟨Q, e, hdiv⟩ := secondBlock_polynomialDivisibility_at_zero F
    twoBlockSecondWhittakerDeformation ψ μ m h β hβ J hJ ν hν
    τ hτs ℓprime hℓprime P P₀ P₁ hprod hP hreal
  let B := Shahidi.twoBlocks (r + 1) 1 (Nat.succ_pos r) (Nat.succ_pos 0)
  have hsize : ∀ i : Fin 2, B.size i = m i + 1 := by
    intro i
    fin_cases i <;> rfl
  let Ebase := oppositeInducedEquiv_of_sizes F B m hsize h
    (Shahidi.pairFamily σ (rankOneExtensionCharacter.{uF,uV} F χ)) β (by
      intro i
      fin_cases i <;> rfl)
  let E := (secondBlockZeroEquiv F m h β).trans Ebase.symm
  refine ⟨P, P₀, P₁, ?_, hP₀, hP₁, Q, e, hdiv⟩
  exact (isPadicSymmetricLPolynomial_comm F ψ μ _ τ P).mp
    ((IsPadicSymmetricLPolynomial.congr_equiv E (Representation.Equiv.refl τ)).mp hP)

end Langlands.RankinSelberg.Padic
