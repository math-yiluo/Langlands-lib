import Langlands.Representation.RankinSelberg.AdjacentRankGammaSocle
import Langlands.Representation.RankinSelberg.AdjacentRankInducedModelContinuation
import Langlands.Representation.RankinSelberg.EqualRankFactorSwapProof

noncomputable section

namespace Langlands.RankinSelberg.Padic

open MeasureTheory HarmonicAnalysis Whittaker QuotientIntegration GeneralLinear
open scoped BigOperators

universe uF uV uW uU

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance largeTwistGammaTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance largeTwistGammaValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance largeTwistGammaLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance largeTwistGammaFieldT2 : T2Space F.Carrier :=
  F.canonicalTopologicalData.fieldT2
local instance largeTwistGammaFieldTotallyDisconnected :
    TotallyDisconnectedSpace F.Carrier := by
  let : NonarchimedeanRing F.Carrier := by
    convert! ValuativeRel.nonarchimedeanRing F.Carrier
    exact Valuation.toTopologicalSpace_eq _
  infer_instance
local instance largeTwistGammaFieldMeasurable : MeasurableSpace F.Carrier := borel _
local instance largeTwistGammaFieldBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance largeTwistGammaGroupMeasurable (r : ℕ) :
    MeasurableSpace (GeneralLinear (r + 1) F.Carrier) := borel _
local instance largeTwistGammaGroupBorel (r : ℕ) :
    BorelSpace (GeneralLinear (r + 1) F.Carrier) := ⟨rfl⟩
local instance largeTwistGammaUnipotentMeasurable (r : ℕ) : MeasurableSpace
    (upperUnipotent (r + 1) F.Carrier) := borel _
local instance largeTwistGammaUnipotentBorel (r : ℕ) : BorelSpace
    (upperUnipotent (r + 1) F.Carrier) := ⟨rfl⟩
local instance largeTwistGammaQuotientMeasurable (r : ℕ) : MeasurableSpace
    (LeftUnipotentQuotient r F.Carrier) := borel _
local instance largeTwistGammaQuotientBorel (r : ℕ) : BorelSpace
    (LeftUnipotentQuotient r F.Carrier) := ⟨rfl⟩

local notation "abv" => normalizedAbsoluteValue F.canonicalTopologicalData
local notation "qF" => F.canonicalTopologicalData.residueCardinality

/-- Complete symmetric gamma certificates commute for full-type inputs,
including the equal-rank branch. -/
theorem isPadicSymmetricGammaFactor_comm
    (ψ : UnitaryAdditiveCharacter F.Carrier) (μ : AdditiveHaarMeasure F.Carrier)
    {r n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {V' : Type uW} [AddCommGroup V'] [Module ℂ V']
    (π : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (τ : Representation ℂ (GeneralLinear (n + 1) F.Carrier) V')
    (hπ : IsOfWhittakerType r (standardCharacter ψ r) π)
    (hτ : IsOfWhittakerType n (standardCharacter ψ n) τ)
    (G : RationalFunctions) :
    IsPadicSymmetricGammaFactor F ψ μ π τ G ↔
      IsPadicSymmetricGammaFactor F ψ μ τ π G := by
  by_cases hnr : n < r
  · rw [isPadicSymmetricGammaFactor_of_le hnr.le,
      isPadicSymmetricGammaFactor_of_lt hnr]
  · by_cases hrn : r < n
    · rw [isPadicSymmetricGammaFactor_of_lt hrn,
        isPadicSymmetricGammaFactor_of_le hrn.le]
    · have heq : n = r := by omega
      subst n
      rw [isPadicSymmetricGammaFactor_of_le le_rfl,
        isPadicSymmetricGammaFactor_of_le le_rfl]
      exact isPadicPairGammaFactor_swap_equalRank F ψ μ π τ hπ hτ G

/-- Actual complete gamma products on the normalized lower induction,
for every real second twist above one bound. -/
def AdjacentRankLargeTwistGamma
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
    ∃ G₀ G₁ : RationalFunctions,
      IsPadicSymmetricGammaFactor F ψ μ τ σ G₀ ∧
      IsPadicSymmetricGammaFactor F ψ μ τ
        (rankOneExtensionCharacter.{uF, uV} F χ) G₁ ∧
      IsPadicSymmetricGammaFactor F ψ μ τ ρ (G₀ * G₁)

/-- The published whole-image realization and arbitrary-test gamma comparison
supply every complete certificate for the actual large-twist lower induction. -/
theorem adjacentRankLargeTwistGamma
    (ψ : UnitaryAdditiveCharacter F.Carrier) (μ : AdditiveHaarMeasure F.Carrier)
    (hself : IsSelfDual ψ μ) {r : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {V' : Type uW} [AddCommGroup V'] [Module ℂ V']
    (σ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (τ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V')
    (hσ : IsOfWhittakerType r (standardCharacter ψ r) σ)
    (hτ : IsOfWhittakerType r (standardCharacter ψ r) τ)
    (χ₀ : Quasicharacter F.Carrier) :
    AdjacentRankLargeTwistGamma F ψ μ σ τ χ₀ := by
  obtain ⟨ℓ, hℓ⟩ := hσ.exists_ne_zero
  have hτs : IsOfWhittakerType r (standardCharacter (ψ.scale (-1)) r) τ := by
    simpa only [standardCharacter_scale_neg_one] using
      (isOfWhittakerType_standard_iff_inverse ψ τ).mp hτ
  obtain ⟨ℓ', hℓ'⟩ := hτs.exists_ne_zero
  let : Measure.IsMulRightInvariant (unipotentHaar F.Carrier r) :=
    unipotentHaar_isMulRightInvariant F.Carrier r
  let ν := unipotentQuotientHaar F.Carrier r
  have hν := unipotentQuotientHaar_isCompatible F.Carrier r
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
  obtain ⟨G₀, G₁, hG₀, hG₁, hG⟩ :=
    adjacentRankImage_gammaFactorization F ψ μ hself ν hν
      σ hσ ℓ hℓ χ ρ hρ J hJ himage τ hτs ℓ' hℓ'
  let eχ : (rankOneCharacter χ.toMonoidHom).Equiv
      (rankOneExtensionCharacter.{uF, uV} F χ) :=
    Representation.Equiv.mk ULift.moduleEquiv.symm (by intro g; rfl)
  exact ⟨G₀, G₁,
    (isPadicSymmetricGammaFactor_comm F ψ μ σ τ hσ hτ G₀).mp hG₀,
    (IsPadicSymmetricGammaFactor.congr_equiv (Representation.Equiv.refl τ) eχ).mp hG₁,
    (isPadicSymmetricGammaFactor_comm F ψ μ ρ τ hρ hτ (G₀ * G₁)).mp hG⟩

end Langlands.RankinSelberg.Padic
