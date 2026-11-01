import Langlands.Representation.RankinSelberg.PadicPairLPolynomialNormalization
import Langlands.Representation.RankinSelberg.AdjacentRankFixedGamma
import Langlands.Representation.RankinSelberg.AdjacentRankSecondBlockLDivisibility

noncomputable section

namespace Langlands.RankinSelberg.Padic

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration
open scoped BigOperators

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance lowerGammaTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance lowerGammaValuation : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance lowerGammaLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance lowerGammaT2 : T2Space F.Carrier :=
  F.canonicalTopologicalData.fieldT2
local instance lowerGammaTotallyDisconnected : TotallyDisconnectedSpace F.Carrier := by
  let : NonarchimedeanRing F.Carrier := by
    convert! ValuativeRel.nonarchimedeanRing F.Carrier
    exact Valuation.toTopologicalSpace_eq _
  infer_instance
local instance lowerGammaMeasurable : MeasurableSpace F.Carrier := borel _
local instance lowerGammaBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance lowerGammaGroupMeasurable (r : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (r + 1) F.Carrier) := borel _
local instance lowerGammaGroupBorel (r : ℕ) :
    BorelSpace (Langlands.GeneralLinear (r + 1) F.Carrier) := ⟨rfl⟩
local instance lowerGammaUnipotentMeasurable (r : ℕ) :
    MeasurableSpace (upperUnipotent (r + 1) F.Carrier) := borel _
local instance lowerGammaUnipotentBorel (r : ℕ) :
    BorelSpace (upperUnipotent (r + 1) F.Carrier) := ⟨rfl⟩
local instance lowerGammaQuotientMeasurable (r : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient r F.Carrier) := borel _
local instance lowerGammaQuotientBorel (r : ℕ) :
    BorelSpace (LeftUnipotentQuotient r F.Carrier) := ⟨rfl⟩

local notation "abv" => normalizedAbsoluteValue F.canonicalTopologicalData
local notation "qF" => F.canonicalTopologicalData.residueCardinality

/-- Complete block and product gamma certificates for the actual ordered
lower adjacent-rank induction with an arbitrary character. -/
def AdjacentRankLowerCharacterGamma
    (ψ : UnitaryAdditiveCharacter F.Carrier) (μ : AdditiveHaarMeasure F.Carrier)
    {r : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (τ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) W)
    (χ : Quasicharacter F.Carrier) : Prop :=
  let B := Shahidi.twoBlocks (r + 1) 1 (Nat.succ_pos r) (Nat.succ_pos 0)
  let ρ := F.canonicalNormalizedOppositeParabolicInduced B
    (B.blockTensor (Shahidi.pairFamily σ (rankOneExtensionCharacter.{uF,uV} F χ)))
  ∃ G₀ G₁ : RationalFunctions,
    IsPadicSymmetricGammaFactor F ψ μ τ σ G₀ ∧
    IsPadicSymmetricGammaFactor F ψ μ τ
      (rankOneExtensionCharacter.{uF,uV} F χ) G₁ ∧
    IsPadicSymmetricGammaFactor F ψ μ τ ρ (G₀ * G₁)

/-- Retained-kernel continuation removes the large-real-twist restriction,
conditional only on complete unramified gamma transport. -/
theorem adjacentRankLowerCharacterGamma_of_transport
    (H : UnramifiedTwistGammaStatement.{uF,uW,uV})
    (ψ : UnitaryAdditiveCharacter F.Carrier) (μ : AdditiveHaarMeasure F.Carrier)
    (hself : IsSelfDual ψ μ) {r : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (τ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) W)
    (hσ : IsOfWhittakerType r (standardCharacter ψ r) σ)
    (hτ : IsOfWhittakerType r (standardCharacter ψ r) τ)
    (χ : Quasicharacter F.Carrier) :
    AdjacentRankLowerCharacterGamma F ψ μ σ τ χ := by
  let m : Fin 2 → ℕ := ![r, 0]
  let h : ∑ i, (m i + 1) = (r + 1) + 1 := adjacentLowerPair_sum r
  let β := adjacentLowerPairBlocks F σ χ
  have hβ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (β i) := by
    intro i
    fin_cases i
    · exact hσ
    · exact rankOneExtensionCharacter_isOfWhittakerType F ψ χ
  obtain ⟨P₀, P₁, CL, hP₀, hP₁, hcert⟩ :=
    adjacentLowerPair_fixedRealRayCertificates F ψ μ hself σ τ hσ hτ χ
  have hc₀ := IsPadicSymmetricLPolynomial.coeff_zero hP₀
  have hc₁ := IsPadicSymmetricLPolynomial.coeff_zero hP₁
  have hprod : P₀ * P₁ ≠ 0 := by
    intro hz
    have hc : (P₀ * P₁).coeff 0 = 1 := by
      simp only [Polynomial.mul_coeff_zero, hc₀, hc₁, one_mul]
    simp only [hz, Polynomial.coeff_zero, zero_ne_one] at hc
  obtain ⟨G₀, G₁, CG, hG₀, hG₁, hgamma⟩ :=
    adjacentLowerPair_fixedRealRayGammaCertificates_of_transport F H ψ μ hself
      σ τ hσ hτ χ
  let C := max CL CG
  have hcertC : SecondBlockCorankRealRayCertificates F ψ μ m h β τ P₀ P₁ C :=
    fun u hu => hcert u (lt_of_le_of_lt (le_max_left CL CG) hu)
  have hgammaC : SecondBlockCorankRealRayGammaCertificates F ψ μ m h β τ G₀ G₁ C :=
    fun u hu => hgamma u (lt_of_le_of_lt (le_max_right CL CG) hu)
  let ρ₀ := twoBlockSecondDeformedInduced F m h β 0
  have hρ₀ : IsOfWhittakerType (r + 1) (standardCharacter ψ (r + 1)) ρ₀ :=
    secondBlockZero_isOfWhittakerType F m h β ψ hβ
  let μsd : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ := ⟨μ, hself⟩
  let g := padicSymmetricGammaFactorOfWhittakerType F ψ μ ρ₀ τ
    (whittakerTypeGammaConstructionInput p F ψ μsd (r + 1) r _ W ρ₀ τ hρ₀ hτ)
  have hg : IsUnequalRankGammaFactor (Nat.lt_succ_self r) qF ψ abv μ ρ₀ τ
      (g.val : RationalFunctions) :=
    (isPairGammaFactor_of_lt (Nat.lt_succ_self r)).mp
      ((isPadicSymmetricGammaFactor_of_le (Nat.le_succ r)).mp g.property)
  obtain ⟨hinv, ν, hν⟩ := hg.1
  let := hinv
  obtain ⟨J, hJ⟩ := hg.2.1
  obtain ⟨ℓprime, hℓprime⟩ := hg.2.2.1
  obtain ⟨ζ, hζ, hall⟩ := hg.2.2.2 ν hν J ℓprime hJ hℓprime
  obtain ⟨⟨R, hRmem, hRzero⟩, hFE⟩ := hall 0 0 rfl
  rw [unequalRankValuesAt_eq] at hRmem
  obtain ⟨U₀, Wprime, hR⟩ := hRmem
  obtain ⟨R₁, Rd₁, hR₁, hRd₁, hN₁⟩ := hFE U₀ Wprime
  have hR₁zero : R₁ ≠ 0 := by
    rwa [← hR.unique F.canonicalTopologicalData.residueCardinality_gt_one hR₁]
  have hτinv := (isOfWhittakerType_standard_iff_inverse ψ τ).mp hτ
  have hclear := secondBlock_realRayClearing_of_certificates F ψ m h β hβ ν hν μ
    τ hτinv ℓprime hℓprime Wprime P₀ P₁ hc₀ hc₁ C hcertC
  obtain ⟨R₂, Rd₂, hR₂, hRd₂, hN₂⟩ :=
    secondBlock_corankGamma_at_zero F ψ m h β hβ J hJ U₀ ν hν μ
      τ hτinv ℓprime hℓprime Wprime ζ hζ G₀ G₁ P₀ P₁ hprod C hclear hgammaC
  have hR₁c := RationalContinuationLinear.continuation_of_eq_on_right hR₁
    ⟨0, fun s _ => corankOneIntegral_eq_zeroZero F ψ ν μ U₀.val Wprime.val s⟩
  have he : R₁ = R₂ :=
    hR₁c.unique F.canonicalTopologicalData.residueCardinality_gt_one hR₂
  have hed : Rd₁ = Rd₂ :=
    hRd₁.unique F.canonicalTopologicalData.residueCardinality_gt_one hRd₂
  have hgeq : (g.val : RationalFunctions) = G₀ * G₁ :=
    GammaFunctionalEquation.gamma_unique F.canonicalTopologicalData.residueCardinality_gt_one
      hR₁zero hN₁ (by simpa only [he, hed] using hN₂)
  have hgprod : IsPadicSymmetricGammaFactor F ψ μ ρ₀ τ (G₀ * G₁) := by
    rw [← hgeq]
    exact g.property
  let B := Shahidi.twoBlocks (r + 1) 1 (Nat.succ_pos r) (Nat.succ_pos 0)
  have hsize : ∀ i : Fin 2, B.size i = m i + 1 := by
    intro i
    fin_cases i <;> rfl
  let Ebase := oppositeInducedEquiv_of_sizes F B m hsize h
    (Shahidi.pairFamily σ (rankOneExtensionCharacter.{uF,uV} F χ)) β (by
      intro i
      fin_cases i <;> rfl)
  let E := (secondBlockZeroEquiv F m h β).trans Ebase.symm
  refine ⟨G₀, G₁, hG₀, hG₁, ?_⟩
  have hρ := adjacentRankNormalizedOpposite_isOfWhittakerType F ψ σ hσ χ
  exact (isPadicSymmetricGammaFactor_comm F ψ μ _ τ hρ hτ (G₀ * G₁)).mp
    ((IsPadicSymmetricGammaFactor.congr_equiv E (Representation.Equiv.refl τ)).mp hgprod)

end Langlands.RankinSelberg.Padic
