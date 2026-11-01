import Langlands.Representation.RankinSelberg.AdjacentRankCorankGammaContinuation
import Langlands.Representation.RankinSelberg.AdjacentRankFixedPolynomials
import Langlands.Representation.RankinSelberg.AdjacentRankLargeTwistGamma
import Langlands.Representation.RankinSelberg.UnramifiedTwistGammaStatement

noncomputable section

namespace Langlands.RankinSelberg.Padic

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration
open scoped BigOperators

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance fixedGammaTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance fixedGammaValuation : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance fixedGammaLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance fixedGammaT2 : T2Space F.Carrier :=
  F.canonicalTopologicalData.fieldT2
local instance fixedGammaTotallyDisconnected : TotallyDisconnectedSpace F.Carrier := by
  let : NonarchimedeanRing F.Carrier := by
    convert! ValuativeRel.nonarchimedeanRing F.Carrier
    exact Valuation.toTopologicalSpace_eq _
  infer_instance
local instance fixedGammaMeasurable : MeasurableSpace F.Carrier := borel _
local instance fixedGammaBorel : BorelSpace F.Carrier := ⟨rfl⟩

/-- Supplied complete unramified gamma transport applies to the actual
determinant-power twist. -/
theorem symmetricGammaFactor_determinantComplexPower_of_transport
    (H : UnramifiedTwistGammaStatement.{uF,uV,uW})
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (μ : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    {r n : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
    (u : ℂ) (G : RationalFunctions)
    (hG : IsPadicSymmetricGammaFactor F ψ μ.val π σ G) :
    IsPadicSymmetricGammaFactor F ψ μ.val π
      (Langlands.twist (F.canonicalTopologicalData.determinantComplexPower (n + 1) u) σ)
      (rationalRescale (spectralShiftUnit F.canonicalTopologicalData.residueCardinality
        F.canonicalTopologicalData.residueCardinality_gt_one u) G) := by
  let T := F.canonicalTopologicalData
  let χ := T.unramifiedCharacter
    (LocalFactor.spectralParameter T.residueCardinality T.residueCardinality_real_pos u)
  have hχ : ∀ x : F.Carrierˣ,
      (χ x : ℂ) = (T.normalizedAbs (x : F.Carrier) : ℂ) ^ u := by
    intro x
    simpa only [T.determinantNorm_scalar, pow_one, T.normalizedAbsUnits_coe,
      PadicField.TopologicalData.determinantComplexPower,
      PadicField.TopologicalData.determinantUnramifiedCharacter, MonoidHom.comp_apply,
      GeneralLinear.determinant, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin] using
      T.determinantComplexPower_apply 1 u (GeneralLinear.scalar x)
  exact (H p F ψ μ r n π σ u χ hχ G hG).1

/-- Fixed complete block gamma certificates with their spectral product on
one real ray of the actual ordered lower family. -/
def AdjacentLowerPairFixedRealRayGammaCertificates
    (ψ : UnitaryAdditiveCharacter F.Carrier) (μ : AdditiveHaarMeasure F.Carrier)
    {r : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (τ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) W)
    (χ : Quasicharacter F.Carrier) : Prop :=
  ∃ (G₀ G₁ : RationalFunctions) (C : ℝ),
    IsPadicSymmetricGammaFactor F ψ μ τ σ G₀ ∧
    IsPadicSymmetricGammaFactor F ψ μ τ
      (rankOneExtensionCharacter.{uF,uV} F χ) G₁ ∧
    SecondBlockCorankRealRayGammaCertificates F ψ μ ![r, 0] (adjacentLowerPair_sum r)
      (adjacentLowerPairBlocks F σ χ) τ G₀ G₁ C

/-- Complete-certificate uniqueness and supplied unramified transport fix
the two factors in the actual large-second-twist gamma theorem. -/
theorem adjacentLowerPair_fixedRealRayGammaCertificates_of_transport
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
    AdjacentLowerPairFixedRealRayGammaCertificates F ψ μ σ τ χ := by
  let μsd : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ := ⟨μ, hself⟩
  let g₀ := padicSymmetricGammaFactorOfWhittakerType F ψ μ τ σ
    (whittakerTypeGammaConstructionInput p F ψ μsd r r W V τ σ hτ hσ)
  let g₁ := padicSymmetricGammaFactorOfWhittakerType F ψ μ τ
    (rankOneExtensionCharacter.{uF,uV} F χ)
    (whittakerTypeGammaConstructionInput p F ψ μsd r 0 W (ULift.{uV} ℂ)
      τ (rankOneExtensionCharacter.{uF,uV} F χ) hτ
      (rankOneExtensionCharacter_isOfWhittakerType F ψ χ))
  obtain ⟨C, hC⟩ := adjacentRankLargeTwistGamma F ψ μ hself σ τ hσ hτ χ
  refine ⟨(g₀.val : RationalFunctions), (g₁.val : RationalFunctions), C,
    g₀.property, g₁.property, ?_⟩
  intro u hu
  obtain ⟨G₀u, G₁u, hG₀u, hG₁u, hG⟩ := hC u hu
  have h₀ : G₀u = (g₀.val : RationalFunctions) := hG₀u.unique g₀.property
  have hG₁twist := symmetricGammaFactor_determinantComplexPower_of_transport F H ψ μsd τ
    (rankOneExtensionCharacter.{uF,uV} F χ) (u : ℂ) (g₁.val : RationalFunctions) g₁.property
  rw [rankOneExtensionCharacter_realTwisted F χ u] at hG₁twist
  have h₁ : G₁u = rationalRescale
      (spectralShiftUnit F.canonicalTopologicalData.residueCardinality
        F.canonicalTopologicalData.residueCardinality_gt_one (u : ℂ))
      (g₁.val : RationalFunctions) := hG₁u.unique hG₁twist
  have hρ := adjacentRankNormalizedOpposite_isOfWhittakerType F ψ σ hσ
    (AdjacentCompactMatrix.realTwistedCharacter F χ u)
  apply (IsPadicSymmetricGammaFactor.congr_equiv
    (adjacentLowerPair_realTwistEquiv F σ χ u) (Representation.Equiv.refl τ)).mp
  apply (isPadicSymmetricGammaFactor_comm F ψ μ _ τ hρ hτ _).mpr
  simpa only [h₀, h₁, AdjacentGammaContinuation.spectralGammaProduct] using hG

end Langlands.RankinSelberg.Padic
