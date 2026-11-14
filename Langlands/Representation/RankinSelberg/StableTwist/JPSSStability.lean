import Langlands.Representation.RankinSelberg.StableTwist.GammaCharacterChange
import Langlands.Representation.RankinSelberg.PairGammaTwistExchangeStatement
import Langlands.Representation.RankinSelberg.HighlyRamifiedProof
import Langlands.Representation.RankinSelberg.HighlyRamifiedGammaAssembly
import Langlands.Representation.RankinSelberg.AdjacentRankLargeTwistGamma
import Langlands.Representation.RankinSelberg.PadicGenericGammaExpression
import Langlands.Representation.RankinSelberg.GenericModel
import Langlands.Representation.RankinSelberg.HighlyRamified.EssentialInput

/-!
# Highly ramified stability of pair gamma factors in both factors
-/

noncomputable section

namespace Langlands.RankinSelberg.StableTwist

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear

universe uF uV uW

variable {p : ℕ} [Fact p.Prime]

/-- Two-factor highly ramified stability for an additive character of conductor `0`. -/
theorem pairGammaStability_conductorZero
    (hR1 : PairGammaTwistExchangeStatement.{uF, uV, uW})
    (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    (hψ : F.canonicalTopologicalData.additiveConductor ψ = 0)
    {r t : ℕ} {V₁ V₂ : Type uV} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂]
    [Module ℂ V₂] {W₁ W₂ : Type uW} [AddCommGroup W₁] [Module ℂ W₁] [AddCommGroup W₂]
    [Module ℂ W₂]
    (π₁ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V₁)
    (π₂ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V₂)
    (σ₁ : Representation ℂ (Langlands.GeneralLinear (t + 1) F.Carrier) W₁)
    (σ₂ : Representation ℂ (Langlands.GeneralLinear (t + 1) F.Carrier) W₂)
    (hπ₁ : letI := F.canonicalTopologicalData.topology; Whittaker.IsGeneric ψ r π₁)
    (hπ₂ : letI := F.canonicalTopologicalData.topology; Whittaker.IsGeneric ψ r π₂)
    (hσ₁ : letI := F.canonicalTopologicalData.topology; Whittaker.IsGeneric ψ t σ₁)
    (hσ₂ : letI := F.canonicalTopologicalData.topology; Whittaker.IsGeneric ψ t σ₂)
    (hπ : SameGLCentralCharacter F π₁ π₂) (hσ : SameGLCentralCharacter F σ₁ σ₂) :
    ∃ A : ℕ, ∀ χ : (letI := F.canonicalTopologicalData.topology; Quasicharacter F.Carrier),
      A ≤ F.canonicalTopologicalData.multiplicativeConductor χ →
      ∀ G G' : RationalFunctions,
        IsPadicSymmetricGammaFactor F ψ ν.val
          (Langlands.twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) π₁) σ₁ G →
        IsPadicSymmetricGammaFactor F ψ ν.val
          (Langlands.twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) π₂) σ₂ G' →
        G = G' := by
  let := F.canonicalTopologicalData.topology
  obtain ⟨A₁, hA₁⟩ := highlyRamifiedGammaStability.{uF, uV, uW} p F ψ ν hψ r t π₁ π₂ σ₁
    hπ₁ hπ₂ hσ₁ hπ
  obtain ⟨A₂, hA₂⟩ := highlyRamifiedGammaStability.{uF, uW, uV} p F ψ ν hψ t r σ₁ σ₂ π₂
    hσ₁ hσ₂ hπ₂ hσ
  refine ⟨max A₁ A₂, fun χ hχ G G' hG hG' => ?_⟩
  obtain ⟨G₁, hG₁a, hG₁b⟩ := hA₁ χ (le_of_max_le_left hχ)
  obtain ⟨G₂, hG₂a, hG₂b⟩ := hA₂ χ (le_of_max_le_right hχ)
  have hWπ₂ := isOfWhittakerType_of_isGeneric F hπ₂
  have hWσ₁ := isOfWhittakerType_of_isGeneric F
    (isGeneric_quasicharacter_twist_iff F.canonicalTopologicalData ψ χ σ₁ |>.mpr hσ₁)
  have hWσ₂ := isOfWhittakerType_of_isGeneric F
    (isGeneric_quasicharacter_twist_iff F.canonicalTopologicalData ψ χ σ₂ |>.mpr hσ₂)
  -- move the gamma factors of `(σᵢ ⊗ χ, π₂)` to `(π₂ ⊗ χ, σᵢ)`
  have h₁ : IsPadicSymmetricGammaFactor F ψ ν.val
      (Langlands.twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) π₂) σ₁ G₂ :=
    (hR1 p F ψ ν.val r t π₂ σ₁ χ G₂).mpr
      ((Padic.isPadicSymmetricGammaFactor_comm F ψ ν.val π₂ _ hWπ₂ hWσ₁ G₂).mpr hG₂a)
  have h₂ : IsPadicSymmetricGammaFactor F ψ ν.val
      (Langlands.twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) π₂) σ₂ G₂ :=
    (hR1 p F ψ ν.val r t π₂ σ₂ χ G₂).mpr
      ((Padic.isPadicSymmetricGammaFactor_comm F ψ ν.val π₂ _ hWπ₂ hWσ₂ G₂).mpr hG₂b)
  rw [hG.unique hG₁a, hG₁b.unique h₁, h₂.unique hG']

/-- Every nontrivial additive character is a scaling `ψ₀^b` of one of conductor `0`. -/
theorem exists_conductorZero_scale (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier) :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.valuativeRel
    letI := F.canonicalTopologicalData.localField
    ∃ (ψ₀ : UnitaryAdditiveCharacter F.Carrier) (b : F.Carrierˣ),
      F.canonicalTopologicalData.additiveConductor ψ₀ = 0 ∧ ψ₀.scale b = ψ := by
  let T := F.canonicalTopologicalData
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have hϖ : T.uniformizer ≠ 0 := by
    intro h
    have h1 := T.ord_uniformizer
    rw [h, T.ord_zero] at h1
    exact zero_ne_one h1
  let a : F.Carrierˣ := (Units.mk0 T.uniformizer hϖ) ^ (-T.additiveConductor ψ)
  refine ⟨ψ.scale a, a⁻¹, ?_, ?_⟩
  · rw [T.additiveConductor_scale]
    simp only [a, Units.val_zpow_eq_zpow_val, Units.val_mk0, T.ord_zpow, T.ord_uniformizer]
    ring
  · rw [UnitaryAdditiveCharacter.scale_scale, mul_inv_cancel,
      UnitaryAdditiveCharacter.scale_one]

/-- **Two-factor highly ramified stability of generic pair gamma factors**, for any
additive character `ψ` and self-dual measure: if `π₁, π₂` (resp. `σ₁, σ₂`) are generic
with equal central characters, then for every quasicharacter `χ` of large conductor the
gamma factors of `(π₁ ⊗ χ, σ₁)` and `(π₂ ⊗ χ, σ₂)` coincide. -/
theorem pairGammaStability
    (hR1 : PairGammaTwistExchangeStatement.{uF, uV, uW})
    (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    {r t : ℕ} {V₁ V₂ : Type uV} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂]
    [Module ℂ V₂] {W₁ W₂ : Type uW} [AddCommGroup W₁] [Module ℂ W₁] [AddCommGroup W₂]
    [Module ℂ W₂]
    (π₁ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V₁)
    (π₂ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V₂)
    (σ₁ : Representation ℂ (Langlands.GeneralLinear (t + 1) F.Carrier) W₁)
    (σ₂ : Representation ℂ (Langlands.GeneralLinear (t + 1) F.Carrier) W₂)
    (hπ₁ : letI := F.canonicalTopologicalData.topology; Whittaker.IsGeneric ψ r π₁)
    (hπ₂ : letI := F.canonicalTopologicalData.topology; Whittaker.IsGeneric ψ r π₂)
    (hσ₁ : letI := F.canonicalTopologicalData.topology; Whittaker.IsGeneric ψ t σ₁)
    (hσ₂ : letI := F.canonicalTopologicalData.topology; Whittaker.IsGeneric ψ t σ₂)
    (hπ : SameGLCentralCharacter F π₁ π₂) (hσ : SameGLCentralCharacter F σ₁ σ₂) :
    ∃ A : ℕ, ∀ χ : (letI := F.canonicalTopologicalData.topology; Quasicharacter F.Carrier),
      A ≤ F.canonicalTopologicalData.multiplicativeConductor χ →
      ∀ G G' : RationalFunctions,
        IsPadicSymmetricGammaFactor F ψ ν.val
          (Langlands.twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) π₁) σ₁ G →
        IsPadicSymmetricGammaFactor F ψ ν.val
          (Langlands.twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) π₂) σ₂ G' →
        G = G' := by
  let T := F.canonicalTopologicalData
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  obtain ⟨ψ₀, b, hψ₀, rfl⟩ := exists_conductorZero_scale F ψ
  obtain ⟨ν₀⟩ := HighlyRamified.nonempty_selfDualHaar F ψ₀
  have gen₀ : ∀ {n : ℕ} {U : Type uV} [AddCommGroup U] [Module ℂ U]
      (ρ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) U),
      Whittaker.IsGeneric (ψ₀.scale b) n ρ → Whittaker.IsGeneric ψ₀ n ρ :=
    fun ρ h => (T.isGeneric_iff_character ρ ψ₀ (ψ₀.scale b)).mpr h
  have gen₀' : ∀ {n : ℕ} {U : Type uW} [AddCommGroup U] [Module ℂ U]
      (ρ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) U),
      Whittaker.IsGeneric (ψ₀.scale b) n ρ → Whittaker.IsGeneric ψ₀ n ρ :=
    fun ρ h => (T.isGeneric_iff_character ρ ψ₀ (ψ₀.scale b)).mpr h
  obtain ⟨A, hA⟩ := pairGammaStability_conductorZero hR1 F ψ₀ ν₀ hψ₀ π₁ π₂ σ₁ σ₂
    (gen₀ π₁ hπ₁) (gen₀ π₂ hπ₂) (gen₀' σ₁ hσ₁) (gen₀' σ₂ hσ₂) hπ hσ
  refine ⟨A, fun χ hχ G G' hG hG' => ?_⟩
  obtain ⟨ωπ, hωπ₁, hωπ₂⟩ := hπ
  obtain ⟨ωσ, hωσ₁, hωσ₂⟩ := hσ
  have hπ₁χ := (isGeneric_quasicharacter_twist_iff T ψ₀ χ π₁).mpr (gen₀ π₁ hπ₁)
  have hπ₂χ := (isGeneric_quasicharacter_twist_iff T ψ₀ χ π₂).mpr (gen₀ π₂ hπ₂)
  have hG₀ := genericSymmetricGammaUnit_isPadic F ψ₀ ν₀.val ν₀.property _ σ₁ hπ₁χ
    (gen₀' σ₁ hσ₁)
  have hG₀' := genericSymmetricGammaUnit_isPadic F ψ₀ ν₀.val ν₀.property _ σ₂ hπ₂χ
    (gen₀' σ₂ hσ₂)
  have e₁ := genericGamma_characterChange ψ₀ ν₀ b ν _ σ₁ _ ωσ hπ₁χ (gen₀' σ₁ hσ₁)
    (hasGLCentralCharacter_twist (χ : F.Carrierˣ →* ℂˣ) hωπ₁) hωσ₁ hG₀ hG
  have e₂ := genericGamma_characterChange ψ₀ ν₀ b ν _ σ₂ _ ωσ hπ₂χ (gen₀' σ₂ hσ₂)
    (hasGLCentralCharacter_twist (χ : F.Carrierˣ →* ℂˣ) hωπ₂) hωσ₂ hG₀' hG'
  rw [e₁, e₂, hA χ hχ _ _ hG₀ hG₀']

end Langlands.RankinSelberg.StableTwist
