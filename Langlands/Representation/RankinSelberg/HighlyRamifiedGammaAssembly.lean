import Langlands.Representation.RankinSelberg.HighlyRamifiedStatement
import Langlands.Representation.RankinSelberg.HighlyRamified.Uniform
import Langlands.Representation.RankinSelberg.PadicGenericGammaFactor
import Langlands.Representation.RankinSelberg.RankOneTestReduction
import Langlands.Representation.Whittaker.Twist
import Langlands.Representation.Twist.SubquotientProof
import Langlands.Representation.Twist.AdmissibilityProof

/-!
# Assembly of highly ramified gamma stability from generic gamma factors

Determinant twists by continuous characters preserve genericity and the
same-central-character hypothesis. For fixed generic data, the conclusion of
`HighlyRamifiedGammaStabilityStatement` is equivalent to an equality of the
constructed generic gamma factors `genericSymmetricGammaFactor` of the twists.
The whole statement follows from its uniqueness form, and hence from
level-uniform stability `HighlyRamified.UniformPairStability` for all ranks.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear

universe uF uV uW

variable {p : ℕ} [Fact p.Prime]

/-- A determinant twist by a continuous character of `Fˣ` preserves genericity:
irreducibility, admissibility (the twisting character has open kernel) and a
nonzero standard Whittaker functional (the same linear form). -/
theorem isGeneric_quasicharacter_twist_iff {F : PadicField.{uF} p}
    (T : F.TopologicalData)
    (ψ : letI := T.topology; UnitaryAdditiveCharacter F.Carrier)
    (χ : letI := T.topology; Quasicharacter F.Carrier)
    {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V) :
    letI := T.topology
    Whittaker.IsGeneric ψ n (twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) π) ↔
      Whittaker.IsGeneric ψ n π := by
  let := T.topology
  have hker : IsOpen (((χ : F.Carrierˣ →* ℂˣ).comp (determinant (n := n + 1))).ker :
      Set (Langlands.GeneralLinear (n + 1) F.Carrier)) :=
    (quasicharacter_isOpen_ker T χ).preimage (T.generalLinearDeterminant (n + 1)).continuous
  unfold Whittaker.IsGeneric
  rw [isIrreducible_twist_iff, isAdmissible_twist_iff _ π hker]
  refine and_congr_right' (and_congr_right' ⟨?_, ?_⟩)
  · rintro ⟨ℓ, hℓ⟩
    exact ⟨(determinantTwistFunctionalEquiv ψ (χ : F.Carrierˣ →* ℂˣ) π).symm ℓ, hℓ⟩
  · rintro ⟨ℓ, hℓ⟩
    exact ⟨determinantTwistFunctionalEquiv ψ (χ : F.Carrierˣ →* ℂˣ) π ℓ, hℓ⟩

theorem isGeneric_quasicharacter_twist {F : PadicField.{uF} p}
    (T : F.TopologicalData)
    (ψ : letI := T.topology; UnitaryAdditiveCharacter F.Carrier)
    (χ : letI := T.topology; Quasicharacter F.Carrier)
    {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V}
    (hπ : letI := T.topology; Whittaker.IsGeneric ψ n π) :
    letI := T.topology
    Whittaker.IsGeneric ψ n (twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) π) :=
  (isGeneric_quasicharacter_twist_iff T ψ χ π).mpr hπ

/-- A determinant twist multiplies a central character `ω` of `GL_(n+1)` by
`χ^(n+1)`. -/
theorem hasGLCentralCharacter_twist {F : Type uF} [Field F] {n : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V} {ω : Fˣ →* ℂˣ}
    (χ : Fˣ →* ℂˣ) (h : Classification.HasGLCentralCharacter F (n + 1) ρ ω) :
    Classification.HasGLCentralCharacter F (n + 1)
      (twist (χ.comp determinant) ρ) (ω * χ ^ (n + 1)) := by
  intro c v
  change (χ (Matrix.GeneralLinearGroup.det
      (Matrix.GeneralLinearGroup.scalar (Fin (n + 1)) c)) : ℂ) •
      ρ (Matrix.GeneralLinearGroup.scalar (Fin (n + 1)) c) v = _
  rw [h c v, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, smul_smul]
  simp only [MonoidHom.mul_apply, MonoidHom.pow_apply, map_pow, Units.val_mul,
    Units.val_pow_eq_pow_val, mul_comm]

/-- Equal central characters remain equal after the same determinant twist. -/
theorem sameGLCentralCharacter_twist (F : PadicField.{uF} p) {r : ℕ}
    {V₁ V₂ : Type uV} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
    {π₁ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V₁}
    {π₂ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V₂}
    (χ : F.Carrierˣ →* ℂˣ) (h : SameGLCentralCharacter F π₁ π₂) :
    SameGLCentralCharacter F (twist (χ.comp determinant) π₁)
      (twist (χ.comp determinant) π₂) := by
  obtain ⟨ω, h₁, h₂⟩ := h
  exact ⟨ω * χ ^ (r + 1), hasGLCentralCharacter_twist χ h₁,
    hasGLCentralCharacter_twist χ h₂⟩

section Canonical

local instance highlyRamifiedAssemblyNormedField (F : PadicField.{uF} p) :
    NontriviallyNormedField F.Carrier :=
  F.canonicalNormedField

/-- For generic `π₁, π₂, σ`, two twists share a gamma factor against `σ`
exactly when their constructed generic gamma factors are equal. -/
theorem exists_common_twist_gammaFactor_iff (F : PadicField.{uF} p)
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    {r t : ℕ} {V₁ V₂ : Type uV} [AddCommGroup V₁] [Module ℂ V₁]
    [AddCommGroup V₂] [Module ℂ V₂] {W : Type uW} [AddCommGroup W] [Module ℂ W]
    {π₁ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V₁}
    {π₂ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V₂}
    {σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F.Carrier) W}
    (hπ₁ : Whittaker.IsGeneric ψ r π₁) (hπ₂ : Whittaker.IsGeneric ψ r π₂)
    (hσ : Whittaker.IsGeneric ψ t σ) (χ : Quasicharacter F.Carrier) :
    (∃ G : RationalFunctions,
        IsPadicSymmetricGammaFactor F ψ ν.val
          (twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) π₁) σ G ∧
        IsPadicSymmetricGammaFactor F ψ ν.val
          (twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) π₂) σ G) ↔
      genericSymmetricGammaFactor F ψ ν.val ν.property
          (twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) π₁) σ
          (isGeneric_quasicharacter_twist F.canonicalTopologicalData ψ χ hπ₁) hσ =
        genericSymmetricGammaFactor F ψ ν.val ν.property
          (twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) π₂) σ
          (isGeneric_quasicharacter_twist F.canonicalTopologicalData ψ χ hπ₂) hσ := by
  constructor
  · rintro ⟨G, h₁, h₂⟩
    exact Units.ext ((genericSymmetricGammaFactor_eq F ψ ν.val ν.property _ σ _ hσ h₁).trans
      (genericSymmetricGammaFactor_eq F ψ ν.val ν.property _ σ _ hσ h₂).symm)
  · intro h
    refine ⟨_, genericSymmetricGammaFactor_isPadic F ψ ν.val ν.property _ σ
      (isGeneric_quasicharacter_twist F.canonicalTopologicalData ψ χ hπ₁) hσ, ?_⟩
    exact (isPadicSymmetricGammaFactor_iff_eq_genericSymmetricGammaFactor F ψ ν.val
      ν.property _ σ (isGeneric_quasicharacter_twist F.canonicalTopologicalData ψ χ hπ₂)
      hσ).mpr (congrArg Units.val h)

/-- The conclusion of `HighlyRamifiedGammaStabilityStatement` for fixed generic
data is equivalent to the same bound for the equality of constructed generic
gamma factors of the twists. -/
theorem exists_bound_common_twist_gammaFactor_iff (F : PadicField.{uF} p)
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    {r t : ℕ} {V₁ V₂ : Type uV} [AddCommGroup V₁] [Module ℂ V₁]
    [AddCommGroup V₂] [Module ℂ V₂] {W : Type uW} [AddCommGroup W] [Module ℂ W]
    {π₁ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V₁}
    {π₂ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V₂}
    {σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F.Carrier) W}
    (hπ₁ : Whittaker.IsGeneric ψ r π₁) (hπ₂ : Whittaker.IsGeneric ψ r π₂)
    (hσ : Whittaker.IsGeneric ψ t σ) :
    (∃ A : ℕ, ∀ χ : Quasicharacter F.Carrier,
      A ≤ F.canonicalTopologicalData.multiplicativeConductor χ →
      ∃ G : RationalFunctions,
        IsPadicSymmetricGammaFactor F ψ ν.val
          (twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) π₁) σ G ∧
        IsPadicSymmetricGammaFactor F ψ ν.val
          (twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) π₂) σ G) ↔
      ∃ A : ℕ, ∀ χ : Quasicharacter F.Carrier,
        A ≤ F.canonicalTopologicalData.multiplicativeConductor χ →
        genericSymmetricGammaFactor F ψ ν.val ν.property
            (twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) π₁) σ
            (isGeneric_quasicharacter_twist F.canonicalTopologicalData ψ χ hπ₁) hσ =
          genericSymmetricGammaFactor F ψ ν.val ν.property
            (twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) π₂) σ
            (isGeneric_quasicharacter_twist F.canonicalTopologicalData ψ χ hπ₂) hσ :=
  exists_congr fun _ => forall_congr' fun χ => imp_congr_right fun _ =>
    exists_common_twist_gammaFactor_iff F ψ ν hπ₁ hπ₂ hσ χ

/-- For fixed generic data, uniqueness of a common gamma factor of the twists
beyond a conductor bound gives the conclusion of
`HighlyRamifiedGammaStabilityStatement`: existence comes from the constructed
generic gamma factors of the twists. -/
theorem exists_bound_common_twist_gammaFactor_of_unique (F : PadicField.{uF} p)
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    {r t : ℕ} {V₁ V₂ : Type uV} [AddCommGroup V₁] [Module ℂ V₁]
    [AddCommGroup V₂] [Module ℂ V₂] {W : Type uW} [AddCommGroup W] [Module ℂ W]
    {π₁ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V₁}
    {π₂ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V₂}
    {σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F.Carrier) W}
    (hπ₁ : Whittaker.IsGeneric ψ r π₁) (hπ₂ : Whittaker.IsGeneric ψ r π₂)
    (hσ : Whittaker.IsGeneric ψ t σ)
    (h : ∃ A : ℕ, ∀ χ : Quasicharacter F.Carrier,
      A ≤ F.canonicalTopologicalData.multiplicativeConductor χ →
      ∀ G₁ G₂ : RationalFunctions,
        IsPadicSymmetricGammaFactor F ψ ν.val
          (twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) π₁) σ G₁ →
        IsPadicSymmetricGammaFactor F ψ ν.val
          (twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) π₂) σ G₂ →
        G₁ = G₂) :
    ∃ A : ℕ, ∀ χ : Quasicharacter F.Carrier,
      A ≤ F.canonicalTopologicalData.multiplicativeConductor χ →
      ∃ G : RationalFunctions,
        IsPadicSymmetricGammaFactor F ψ ν.val
          (twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) π₁) σ G ∧
        IsPadicSymmetricGammaFactor F ψ ν.val
          (twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) π₂) σ G := by
  obtain ⟨A, hA⟩ := h
  refine ⟨A, fun χ hχ => ?_⟩
  have h₁ := genericSymmetricGammaFactor_isPadic F ψ ν.val ν.property _ σ
    (isGeneric_quasicharacter_twist F.canonicalTopologicalData ψ χ hπ₁) hσ
  have h₂ := genericSymmetricGammaFactor_isPadic F ψ ν.val ν.property _ σ
    (isGeneric_quasicharacter_twist F.canonicalTopologicalData ψ χ hπ₂) hσ
  exact ⟨_, h₁, (congrArg (IsPadicSymmetricGammaFactor F ψ ν.val
    (twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) π₂) σ) (hA χ hχ _ _ h₁ h₂)).mpr h₂⟩

end Canonical

namespace HighlyRamified

/-- Gamma stability for candidates of rank `r + 1` and tests of rank `t + 1`, in
uniqueness form. Under the hypotheses of `HighlyRamifiedGammaStabilityStatement`
there is a bound `A` such that, for every quasicharacter `χ` of conductor exponent
at least `A`, any gamma factor of `(π₁ ⊗ χ ∘ det, σ)` equals any gamma factor of
`(π₂ ⊗ χ ∘ det, σ)`. The bound may depend on all the data. -/
def PairStability (r t : ℕ) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ),
    F.canonicalTopologicalData.additiveConductor ψ = 0 →
    ∀ {V₁ V₂ : Type uV} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
      {W : Type uW} [AddCommGroup W] [Module ℂ W]
      (π₁ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V₁)
      (π₂ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V₂)
      (σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F.Carrier) W),
    (letI := F.canonicalTopologicalData.topology; Whittaker.IsGeneric ψ r π₁) →
    (letI := F.canonicalTopologicalData.topology; Whittaker.IsGeneric ψ r π₂) →
    (letI := F.canonicalTopologicalData.topology; Whittaker.IsGeneric ψ t σ) →
    SameGLCentralCharacter F π₁ π₂ →
    ∃ A : ℕ, ∀ χ : (letI := F.canonicalTopologicalData.topology; Quasicharacter F.Carrier),
      A ≤ F.canonicalTopologicalData.multiplicativeConductor χ →
      ∀ G₁ G₂ : RationalFunctions,
        IsPadicSymmetricGammaFactor F ψ ν.val
          (Langlands.twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) π₁) σ G₁ →
        IsPadicSymmetricGammaFactor F ψ ν.val
          (Langlands.twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) π₂) σ G₂ →
        G₁ = G₂

end HighlyRamified

/-- `HighlyRamifiedGammaStabilityStatement` follows from its uniqueness form
`HighlyRamified.PairStability r t` for every pair of ranks. -/
theorem highlyRamifiedGammaStability_of_pairStability
    (h : ∀ r t : ℕ, HighlyRamified.PairStability.{uF, uV, uW} r t) :
    HighlyRamifiedGammaStabilityStatement.{uF, uV, uW} := by
  intro p _ F ψ ν hψ r t V₁ V₂ _ _ _ _ W _ _ π₁ π₂ σ hπ₁ hπ₂ hσ hc
  exact exists_bound_common_twist_gammaFactor_of_unique F ψ ν hπ₁ hπ₂ hσ
    (h r t p F ψ ν hψ π₁ π₂ σ hπ₁ hπ₂ hσ hc)

/-- A generic representation acts on a nontrivial space: its nonzero Whittaker
functional is not a map out of the zero space. -/
theorem nontrivial_of_isGeneric {F : PadicField.{uF} p} (T : F.TopologicalData)
    (ψ : letI := T.topology; UnitaryAdditiveCharacter F.Carrier) {n : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V}
    (hπ : letI := T.topology; Whittaker.IsGeneric ψ n π) : Nontrivial V := by
  let := T.topology
  obtain ⟨ℓ, hℓ⟩ := hπ.2.2
  by_contra hV
  rw [not_nontrivial_iff_subsingleton] at hV
  exact hℓ (LinearMap.ext fun v => by rw [Subsingleton.elim v 0, map_zero, map_zero])

/-- Level-uniform stability gives stability for the same ranks: a generic
representation is smooth on a nontrivial space, so it has a level vector, and
the two candidates share the larger of their levels. -/
theorem HighlyRamified.pairStability_of_uniformPairStability {r t : ℕ}
    (h : HighlyRamified.UniformPairStability.{uF, uV, uW} r t) :
    HighlyRamified.PairStability.{uF, uV, uW} r t := by
  intro p _ F ψ ν hψ V₁ V₂ _ _ _ _ W _ _ π₁ π₂ σ hπ₁ hπ₂ hσ hc
  have := nontrivial_of_isGeneric F.canonicalTopologicalData ψ hπ₁
  have := nontrivial_of_isGeneric F.canonicalTopologicalData ψ hπ₂
  have := nontrivial_of_isGeneric F.canonicalTopologicalData ψ hσ
  obtain ⟨m₁, h₁⟩ := HighlyRamified.exists_hasPrincipalLevelVector F π₁ hπ₁.2.1.1
  obtain ⟨m₂, h₂⟩ := HighlyRamified.exists_hasPrincipalLevelVector F π₂ hπ₂.2.1.1
  obtain ⟨m₃, h₃⟩ := HighlyRamified.exists_hasPrincipalLevelVector F σ hσ.2.1.1
  obtain ⟨A, hA⟩ := h p F ψ ν hψ (max m₁ m₂) m₃
  exact ⟨A, fun χ hχ => hA π₁ π₂ σ hπ₁ hπ₂ hσ (h₁.mono F π₁ (le_max_left m₁ m₂))
    (h₂.mono F π₂ (le_max_right m₁ m₂)) h₃ hc χ hχ⟩

/-- `HighlyRamifiedGammaStabilityStatement` follows from level-uniform
stability for every pair of ranks. -/
theorem highlyRamifiedGammaStability_of_uniformPairStability
    (h : ∀ r t : ℕ, HighlyRamified.UniformPairStability.{uF, uV, uW} r t) :
    HighlyRamifiedGammaStabilityStatement.{uF, uV, uW} :=
  highlyRamifiedGammaStability_of_pairStability fun r t =>
    HighlyRamified.pairStability_of_uniformPairStability (h r t)

end Langlands.RankinSelberg
