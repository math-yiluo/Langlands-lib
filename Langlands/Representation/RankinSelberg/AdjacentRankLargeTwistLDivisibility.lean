import Langlands.Representation.RankinSelberg.AdjacentRankImageLDivisibility
import Langlands.Representation.RankinSelberg.CanonicalPairLFactor
import Langlands.Representation.RankinSelberg.EqualRankFactorSwapProof
import Langlands.Representation.RankinSelberg.WhittakerGammaAdapters

/-! Certified polynomial divisibility for the actual large-second-twist lower induction. -/

noncomputable section

namespace Langlands.RankinSelberg.Padic

open MeasureTheory HarmonicAnalysis Whittaker QuotientIntegration GeneralLinear
open scoped BigOperators

universe uF uV uW uU

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance largeTwistLTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance largeTwistLValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance largeTwistLLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance largeTwistLFieldT2 : T2Space F.Carrier :=
  F.canonicalTopologicalData.fieldT2
local instance largeTwistLFieldTotallyDisconnected :
    TotallyDisconnectedSpace F.Carrier := by
  let : NonarchimedeanRing F.Carrier := by
    convert! ValuativeRel.nonarchimedeanRing F.Carrier
    exact Valuation.toTopologicalSpace_eq _
  infer_instance
local instance largeTwistLFieldMeasurable : MeasurableSpace F.Carrier := borel _
local instance largeTwistLFieldBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance largeTwistLGroupMeasurable (r : ℕ) :
    MeasurableSpace (GeneralLinear (r + 1) F.Carrier) := borel _
local instance largeTwistLGroupBorel (r : ℕ) :
    BorelSpace (GeneralLinear (r + 1) F.Carrier) := ⟨rfl⟩
local instance largeTwistLUnipotentMeasurable (r : ℕ) : MeasurableSpace
    (upperUnipotent (r + 1) F.Carrier) := borel _
local instance largeTwistLUnipotentBorel (r : ℕ) : BorelSpace
    (upperUnipotent (r + 1) F.Carrier) := ⟨rfl⟩
local instance largeTwistLQuotientMeasurable (r : ℕ) : MeasurableSpace
    (LeftUnipotentQuotient r F.Carrier) := borel _
local instance largeTwistLQuotientBorel (r : ℕ) : BorelSpace
    (LeftUnipotentQuotient r F.Carrier) := ⟨rfl⟩

local notation "abv" => normalizedAbsoluteValue F.canonicalTopologicalData
local notation "qF" => F.canonicalTopologicalData.residueCardinality

/-- Additive-character scaling transports the complete supplied-measure
pair certificate, including the compatible-quotient existence witness. -/
theorem isPadicPairLPolynomial_characterChange
    (ψ : UnitaryAdditiveCharacter F.Carrier) (a : F.Carrierˣ)
    (μ : AdditiveHaarMeasure F.Carrier) {r n : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {V' : Type uW} [AddCommGroup V'] [Module ℂ V']
    (π : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (τ : Representation ℂ (GeneralLinear (n + 1) F.Carrier) V')
    (P : Polynomial ℂ) :
    IsPadicPairLPolynomial F ψ μ π τ P ↔
      IsPadicPairLPolynomial F (ψ.scale a) μ π τ P := by
  have : SecondCountableTopology F.Carrier :=
    F.canonicalTopologicalData.secondCountableTopology
  refine and_congr Iff.rfl (forall_congr' fun _ => forall_congr' fun ν => ?_)
  refine imp_congr_right fun hν => ?_
  have heq := unipotentQuotientHaar_unique F.Carrier n ν hν
  subst ν
  exact isPairLPolynomial_characterChange_canonical F.canonicalTopologicalData
    n r ψ a μ π τ P

/-- Both rank orders retain the same full certificate under character scaling. -/
theorem isPadicSymmetricLPolynomial_characterChange
    (ψ : UnitaryAdditiveCharacter F.Carrier) (a : F.Carrierˣ)
    (μ : AdditiveHaarMeasure F.Carrier) {r n : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {V' : Type uW} [AddCommGroup V'] [Module ℂ V']
    (π : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (τ : Representation ℂ (GeneralLinear (n + 1) F.Carrier) V')
    (P : Polynomial ℂ) :
    IsPadicSymmetricLPolynomial F ψ μ π τ P ↔
      IsPadicSymmetricLPolynomial F (ψ.scale a) μ π τ P := by
  unfold IsPadicSymmetricLPolynomial
  split_ifs
  · exact isPadicPairLPolynomial_characterChange F ψ a μ π τ P
  · exact isPadicPairLPolynomial_characterChange F ψ a μ τ π P

/-- Complete symmetric L certificates commute even in the equal-rank branch. -/
theorem isPadicSymmetricLPolynomial_comm
    (ψ : UnitaryAdditiveCharacter F.Carrier) (μ : AdditiveHaarMeasure F.Carrier)
    {r n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {V' : Type uW} [AddCommGroup V'] [Module ℂ V']
    (π : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (τ : Representation ℂ (GeneralLinear (n + 1) F.Carrier) V')
    (P : Polynomial ℂ) :
    IsPadicSymmetricLPolynomial F ψ μ π τ P ↔
      IsPadicSymmetricLPolynomial F ψ μ τ π P := by
  by_cases hnr : n < r
  · rw [isPadicSymmetricLPolynomial_of_le hnr.le,
      isPadicSymmetricLPolynomial_of_lt hnr]
  · by_cases hrn : r < n
    · rw [isPadicSymmetricLPolynomial_of_lt hrn,
        isPadicSymmetricLPolynomial_of_le hrn.le]
    · have heq : n = r := by omega
      subst n
      rw [isPadicSymmetricLPolynomial_of_le le_rfl,
        isPadicSymmetricLPolynomial_of_le le_rfl]
      exact isPadicPairLPolynomial_swap_equalRank F ψ μ π τ P

private theorem symmetricLPolynomial_ne_zero
    (ψ : UnitaryAdditiveCharacter F.Carrier) (μ : AdditiveHaarMeasure F.Carrier)
    {r n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {V' : Type uW} [AddCommGroup V'] [Module ℂ V']
    (π : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (τ : Representation ℂ (GeneralLinear (n + 1) F.Carrier) V')
    (P : Polynomial ℂ) (hP : IsPadicSymmetricLPolynomial F ψ μ π τ P) : P ≠ 0 := by
  unfold IsPadicSymmetricLPolynomial at hP
  split_ifs at hP
  · obtain ⟨⟨hinv, ν, hν⟩, hall⟩ := hP
    let := hinv
    exact (hall ν hν).ne_zero
  · obtain ⟨⟨hinv, ν, hν⟩, hall⟩ := hP
    let := hinv
    exact (hall ν hν).ne_zero

/-- Complete pair-polynomial certificates and the required divisibility on
actual normalized lower induction above one real second-twist threshold. -/
def AdjacentRankLargeTwistLDivisibility
    (ψ : UnitaryAdditiveCharacter F.Carrier) (μ : AdditiveHaarMeasure F.Carrier)
    {r : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {V' : Type uW} [AddCommGroup V'] [Module ℂ V']
    (σ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (τ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V')
    (χ₀ : Quasicharacter F.Carrier) : Prop :=
  ∃ C : ℝ, ∀ u : ℝ, C < u →
    let χ := AdjacentCompactMatrix.realTwistedCharacter F χ₀ u
    let B := Shahidi.twoBlocks (r + 1) 1 (Nat.succ_pos r) (Nat.succ_pos 0)
    let ρ := F.canonicalNormalizedOppositeParabolicInduced B
      (B.blockTensor (Shahidi.pairFamily σ (rankOneExtensionCharacter.{uF, uV} F χ)))
    ∃ P P₀ P₁ : Polynomial ℂ,
      IsPadicSymmetricLPolynomial F ψ μ τ ρ P ∧
      IsPadicSymmetricLPolynomial F ψ μ τ σ P₀ ∧
      IsPadicSymmetricLPolynomial F ψ μ τ (rankOneExtensionCharacter.{uF, uV} F χ) P₁ ∧
      ∃ (Q : Polynomial ℂ) (e : ℕ), Polynomial.X ^ e * (P₀ * P₁) = Q * P

/-- The actual large-second-twist model gives complete L certificates and
exact product divisibility, with every analytic/image/type premise discharged. -/
theorem adjacentRankLargeTwistLDivisibility
    (ψ : UnitaryAdditiveCharacter F.Carrier) (μ : AdditiveHaarMeasure F.Carrier)
    (hself : IsSelfDual ψ μ) {r : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {V' : Type uW} [AddCommGroup V'] [Module ℂ V']
    (σ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (τ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V')
    (hσ : IsOfWhittakerType r (standardCharacter ψ r) σ)
    (hτ : IsOfWhittakerType r (standardCharacter ψ r) τ)
    (χ₀ : Quasicharacter F.Carrier) :
    AdjacentRankLargeTwistLDivisibility F ψ μ σ τ χ₀ := by
  obtain ⟨ℓ, hℓ⟩ := hσ.exists_ne_zero
  have hτs : IsOfWhittakerType r (standardCharacter (ψ.scale (-1)) r) τ := by
    simpa only [standardCharacter_scale_neg_one] using
      (isOfWhittakerType_standard_iff_inverse ψ τ).mp hτ
  obtain ⟨ℓ', hℓ'⟩ := hτs.exists_ne_zero
  let μsd : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ := ⟨μ, hself⟩
  obtain ⟨P₀, hP₀⟩ := symmetricLPolynomialExists p F ψ μsd r r V V' σ τ hσ hτ
  refine ⟨adjacentRankInducedModelBound F ψ μ hself σ hσ ℓ hℓ χ₀, ?_⟩
  intro u hu
  let χ := AdjacentCompactMatrix.realTwistedCharacter F χ₀ u
  let B := Shahidi.twoBlocks (r + 1) 1 (Nat.succ_pos r) (Nat.succ_pos 0)
  let ρ := F.canonicalNormalizedOppositeParabolicInduced B
    (B.blockTensor (Shahidi.pairFamily σ (rankOneExtensionCharacter.{uF, uV} F χ)))
  have hρ : IsOfWhittakerType (r + 1) (standardCharacter ψ (r + 1)) ρ :=
    adjacentRankNormalizedOpposite_isOfWhittakerType F ψ σ hσ χ
  obtain ⟨J, hJ, himage⟩ :=
    (adjacentRankModelImage p F ψ μ hself r V σ hσ ℓ hℓ χ₀).choose_spec u hu
  obtain ⟨P, hP⟩ := symmetricLPolynomialExists p F ψ μsd (r + 1) r _ V' ρ τ hρ hτ
  have hχ : IsOfWhittakerType 0 (standardCharacter ψ 0) (rankOneCharacter (χ : F.Carrierˣ →* ℂˣ)) :=
    rankOneCharacter_isOfWhittakerType p F ψ χ
  obtain ⟨P₁, hP₁⟩ := symmetricLPolynomialExists p F ψ μsd r 0 V' ℂ τ
    (rankOneCharacter (χ : F.Carrierˣ →* ℂˣ)) hτ hχ
  have hcancel : Langlands.twist (((χ : F.Carrierˣ →* ℂˣ)⁻¹).comp determinant)
      (rankOneCharacter (χ : F.Carrierˣ →* ℂˣ)) = rankOneCharacter 1 := by
    have hone : (1 : F.Carrierˣ →* ℂˣ) * (χ : F.Carrierˣ →* ℂˣ) = χ :=
      MonoidHom.ext fun _ => one_mul _
    simpa only [hone] using
      twist_rankOneCharacter (χ := (1 : F.Carrierˣ →* ℂˣ)) (χ : F.Carrierˣ →* ℂˣ)
  have hP₁twist : IsPadicSymmetricLPolynomial F ψ μ
      (Langlands.twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) τ)
      (rankOneCharacter 1) P₁ := by
    simpa only [hcancel] using
      (isPadicSymmetricLPolynomial_twist ψ μ τ
        (rankOneCharacter (χ : F.Carrierˣ →* ℂˣ)) (χ : F.Carrierˣ →* ℂˣ) P₁).mpr hP₁
  have hP₁s := (isPadicSymmetricLPolynomial_characterChange F ψ (-1) μ _ _ P₁).mp hP₁twist
  have hPair : IsPadicPairLPolynomial F ψ μ ρ τ P :=
    (isPadicSymmetricLPolynomial_of_le (Nat.le_succ r)).mp hP
  obtain ⟨⟨hinv, ν, hν⟩, -⟩ := hPair
  let := hinv
  have hbound := adjacentRankImage_productDenominatorBound F ψ μ hself ν hν
    σ hσ ℓ hℓ χ ρ hρ J hJ himage τ hτs ℓ' hℓ' P₀ P₁ hP₀ hP₁s
  have hnonzero : P₀ * P₁ ≠ 0 := mul_ne_zero
    (symmetricLPolynomial_ne_zero F ψ μ σ τ P₀ hP₀)
    (symmetricLPolynomial_ne_zero F ψ μ τ (rankOneCharacter (χ : F.Carrierˣ →* ℂˣ)) P₁ hP₁)
  obtain ⟨Q, e, hdiv⟩ := adjacentRankModelBound_polynomialDivisibility F ψ μ ν hν
    ρ hρ J hJ τ hτs ℓ' hℓ' P (P₀ * P₁) hnonzero hP hbound
  let eχ : (rankOneCharacter (χ : F.Carrierˣ →* ℂˣ)).Equiv
      (rankOneExtensionCharacter.{uF, uV} F χ) :=
    Representation.Equiv.mk ULift.moduleEquiv.symm (by intro g; rfl)
  exact ⟨P, P₀, P₁,
    (isPadicSymmetricLPolynomial_comm F ψ μ ρ τ P).mp hP,
    (isPadicSymmetricLPolynomial_comm F ψ μ σ τ P₀).mp hP₀,
    (IsPadicSymmetricLPolynomial.congr_equiv (Representation.Equiv.refl τ) eχ).mp hP₁,
    Q, e, hdiv⟩

end Langlands.RankinSelberg.Padic
