import Langlands.Representation.RankinSelberg.HighlyRamified.CoreStep
import Langlands.Representation.RankinSelberg.HighlyRamified.AdjacentInduction
import Langlands.Representation.RankinSelberg.HighlyRamified.EssentialInput
import Langlands.Representation.RankinSelberg.HighlyRamified.Duality
import Langlands.Representation.Twist.AlgebraProof

/-!
# The adjacent-rank step

Jacquet and Shalika 1985, §4.4: stability for the pair of ranks `(n + 3, n + 2)` from the
monomial gamma input at rank `n` (`MonomialTwistGamma n`). The proof twists the candidates by the
quasicharacter `ξ` of the essential-vector input (`EssentialPairInput`), writes
`χ = (ξ⁻¹ χ) ξ`, and applies `core_gamma_eq` to `π_i ⊗ ξ ∘ det` and `ξ⁻¹ χ`. The Kirillov shell
vector of the test representation is an input (`KirillovShellInput`).
-/

noncomputable section

namespace Langlands.RankinSelberg.HighlyRamified

open MeasureTheory HarmonicAnalysis Whittaker QuotientIntegration Matrix Langlands.GeneralLinear

universe uF uV uW U

variable {p : ℕ} [Fact p.Prime]

/-- The Kirillov shell input, an internal substitute for the vector `W'` of Jacquet and
Shalika 1985, (4.4.16)–(4.4.17) (see `KirillovShell.md`, Provenance): for a generic
`σ` of rank `m + 2` with central character `ω_σ`, a nonzero `ψ⁻¹`-functional `ℓ'`, a
quasicharacter `χ`, a unit `ϖ` and `c`, a model vector `f'` supported on `N GL_(m+1)(O) ϖ^(-c)`
in the first `m + 1` coordinates, equal to `κ₁ χ(det k)⁻¹` at `diag(k ϖ^(-c), 1)` with
`κ₁ ≠ 0`, and right equivariant under `diag(I, c)`, `c ∈ O^×`, with the character
`ω_σ χ^(m+1)`. -/
def KirillovShellInput : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier),
    F.canonicalTopologicalData.additiveConductor ψ = 0 →
    ∀ (m : ℕ) {W : Type uW} [AddCommGroup W] [Module ℂ W]
      (σ : Representation ℂ (Langlands.GeneralLinear (m + 1 + 1) F.Carrier) W),
      (letI := F.canonicalTopologicalData.topology; Whittaker.IsGeneric ψ (m + 1) σ) →
      ∀ ωσ : F.Carrierˣ →* ℂˣ, Classification.HasGLCentralCharacter F.Carrier (m + 1 + 1) σ ωσ →
      letI := F.canonicalTopologicalData.topology
      letI := F.canonicalTopologicalData.valuativeRel
      ∀ ℓ' : glInverseFunctionals ψ (m + 1) σ, ℓ'.val ≠ 0 →
      ∀ (χ : Quasicharacter F.Carrier) (ϖ : F.Carrierˣ) (c : ℕ),
      ∃ (f' : (coefficientModel σ ℓ').toSubmodule) (κ₁ : ℂ), κ₁ ≠ 0 ∧
        (∀ B : Langlands.GeneralLinear (m + 1) F.Carrier, f'.val.val (rankInclusion 1 B) ≠ 0 →
          ∃ u : upperUnipotent (m + 1) F.Carrier,
            IsIntegralMatrix (u.val * B * Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) (ϖ ^ c))) ∧
        (∀ k : Langlands.GeneralLinear (m + 1) F.Carrier, IsIntegralMatrix k →
          f'.val.val (rankInclusion 1
            (k * Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) (ϖ ^ c)⁻¹)) =
            κ₁ * (((χ : F.Carrierˣ →* ℂˣ) (determinant k) : ℂ))⁻¹) ∧
        (∀ (g : Langlands.GeneralLinear (m + 1 + 1) F.Carrier)
          (c' : lowerTriangularSubgroup 1 F.Carrier), IsIntegralUnit (c'.val 0 0) →
            f'.val.val (g * lowerBlockPair (1 : Langlands.GeneralLinear (m + 1) F.Carrier) 0 c') =
              ((ωσ * (χ : F.Carrierˣ →* ℂˣ) ^ (m + 1)) (determinant c'.val) : ℂ) * f'.val.val g)

section Canonical

variable (F : PadicField.{uF} p)

local instance adjacentStepFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance adjacentStepValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance adjacentStepLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField

/-- A generic representation has a nonzero functional for the inverse standard character. -/
theorem exists_inverseFunctional (ψ : UnitaryAdditiveCharacter F.Carrier) {n : ℕ}
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
    (hσ : IsGeneric ψ n σ) : ∃ ℓ' : glInverseFunctionals ψ n σ, ℓ'.val ≠ 0 := by
  obtain ⟨ℓ, hℓ⟩ := hσ.2.2
  set ℓ₁ := characterChangeFunctionalEquiv ψ σ (-1) ℓ with hℓ₁
  refine ⟨functionalsCongr (standardCharacter_scale_neg_one ψ n) ℓ₁, ?_⟩
  change ℓ₁.val ≠ 0
  intro h0
  apply hℓ
  have : ℓ = 0 := (characterChangeFunctionalEquiv ψ σ (-1)).map_eq_zero_iff.mp (Subtype.ext h0)
  rw [this]
  rfl

/-- `χ = (ξ⁻¹ χ) ξ` on determinants. -/
theorem twist_split (χ ξ : Quasicharacter F.Carrier) {n : ℕ} {V : Type*} [AddCommGroup V]
    [Module ℂ V] (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V) :
    Langlands.twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) π =
      Langlands.twist (((ξ⁻¹ * χ : Quasicharacter F.Carrier) : F.Carrierˣ →* ℂˣ).comp determinant)
        (Langlands.twist ((ξ : F.Carrierˣ →* ℂˣ).comp determinant) π) := by
  rw [twist_twist]
  congr 1
  ext g
  change (χ (determinant g) : ℂ) = ((ξ (determinant g))⁻¹ * χ (determinant g) *
    ξ (determinant g) : ℂˣ)
  rw [mul_comm ((ξ (determinant g))⁻¹), mul_assoc, inv_mul_cancel, mul_one]

end Canonical

/-- The adjacent-rank step: stability for `(n + 2, n + 1)`-indexed pairs (candidates of rank
`n + 3`, tests of rank `n + 2`) from the monomial gamma input at `n`, the completeness lemma,
the essential-vector input and the Kirillov shell input. -/
theorem adjacentStep (hT1 : WhittakerCompletenessStatement.{uF, U})
    (hE : ∀ n, EssentialPairInput.{uF, U} n) (hK : KirillovShellInput.{uF, U}) (n : ℕ)
    (_hIH : UniformPairStability.{uF, U, U} (n + 1) n) (hmono : MonomialTwistGamma.{uF, U} n) :
    UniformPairStability.{uF, U, U} (n + 1 + 1) (n + 1) := by
  intro p _ F ψ ν hψ0 m m'
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  obtain ⟨ξ, f, hf, hEss⟩ := hE n p F ψ hψ0 m
  obtain ⟨A₀, hA₀⟩ := hmono p F ψ ν hψ0 m' f
  refine ⟨max A₀ (F.canonicalTopologicalData.multiplicativeConductor ξ + f + m' + 1), ?_⟩
  intro V₁ V₂ _ _ _ _ W _ _ π₁ π₂ σ hπ₁ hπ₂ hσ hl₁ hl₂ hlσ hsame χ hχA G₁ G₂ hG₁ hG₂
  -- conductors
  set a := F.canonicalTopologicalData.multiplicativeConductor χ with ha_def
  have haA₀ : A₀ ≤ a := le_of_max_le_left hχA
  have haξ : F.canonicalTopologicalData.multiplicativeConductor ξ + f + m' + 1 ≤ a := le_of_max_le_right hχA
  set χ' : Quasicharacter F.Carrier := ξ⁻¹ * χ with hχ'
  have ha' : F.canonicalTopologicalData.multiplicativeConductor χ' = a :=
    multiplicativeConductor_mul_of_lt F χ ξ⁻¹ (by rw [multiplicativeConductor_inv]; omega)
  -- the essential vectors of the `ξ`-twists
  obtain ⟨ℓ₁, ℓ₂, hℓ₁, hℓ₂, w₁, w₂, hw₁, hw₂, hP, hw₁1, hw₂1, htr₁, -⟩ :=
    hEss π₁ π₂ hπ₁ hπ₂ hl₁ hl₂
  obtain ⟨ω₀, hω₁, hω₂⟩ := hsame
  have hc₁ := hasGLCentralCharacter_twist (ξ : F.Carrierˣ →* ℂˣ) hω₁
  have hc₂ := hasGLCentralCharacter_twist (ξ : F.Carrierˣ →* ℂˣ) hω₂
  have hωf := htr₁ _ hc₁
  have hπ₁ξ := isGeneric_quasicharacter_twist F.canonicalTopologicalData ψ ξ hπ₁
  have hπ₂ξ := isGeneric_quasicharacter_twist F.canonicalTopologicalData ψ ξ hπ₂
  -- the test representation
  obtain ⟨ℓ', hℓ'⟩ := exists_inverseFunctional F ψ σ hσ
  obtain ⟨ωσq, hωσ⟩ := exists_quasicharacter_hasGLCentralCharacter F ψ σ hσ
  have hσcond := multiplicativeConductor_le_of_hasGLCentralCharacter F σ ωσq hωσ hlσ
  have hb : 0 < a := by omega
  have hσb := trivialOnPrincipalUnits_of_conductor_le F ωσq hb (by omega)
  have hχb := trivialOnPrincipalUnits_of_conductor_le F χ' hb (by omega)
  set c := (n + 2) * a with hc_def
  have hcb : f + a ≤ c := by rw [hc_def]; nlinarith
  have hcf : f + f ≤ c := by rw [hc_def]; nlinarith
  set ϖ : F.Carrierˣ := LocalFactor.PadicAbelian.uniformizerUnit F.canonicalTopologicalData with hϖ_def
  have hϖ : F.canonicalTopologicalData.ord (ϖ : F.Carrier) = 1 :=
    LocalFactor.PadicAbelian.uniformizerUnit_ord F.canonicalTopologicalData
  -- the Kirillov shell vector
  obtain ⟨f', κ₁, hκ₁, hsupp, hval, hequiv⟩ := hK p F ψ hψ0 n σ hσ ωσq hωσ ℓ' hℓ' χ' ϖ c
  -- the monomial gamma certificates
  have hσi := isGeneric_inverseTransposePullback_of_inverse F ψ σ hσ ℓ' hℓ'
  have hlσi := hasPrincipalLevelVector_inverseTransposePullback F σ hlσ
  obtain ⟨C, hC⟩ := hA₀ (inverseTransposePullback σ) hσi hlσi χ'⁻¹
    (by rw [multiplicativeConductor_inv, ha']; exact haA₀)
  have hPi := isGeneric_twist_inverseTransposePullback F ψ σ hσ ℓ' hℓ'
    (χ' : F.Carrierˣ →* ℂˣ) χ'.continuous
  have hGall : ∀ (X : Type U) [AddCommGroup X] [Module ℂ X]
      (τ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) X)
      (ωτ : F.Carrierˣ →* ℂˣ), IsGeneric ψ n τ → HasPrincipalLevelVector F τ f →
      Classification.HasGLCentralCharacter F.Carrier (n + 1) τ ωτ →
      ∃ G : RationalFunctions, IsPadicPairGammaFactor F ψ ν.val
          (Langlands.twist (((χ' : F.Carrierˣ →* ℂˣ))⁻¹.comp determinant)
            (inverseTransposePullback σ)) τ G ∧
        G = rationalEpsilonMonomial (C ωτ) ((c * (n + 1) : ℕ) : ℤ) := by
    intro X _ _ τ ωτ hτ hτl hτc
    have hsym := genericSymmetricGammaFactor_isPadic F ψ ν.val ν.property _ τ hPi hτ
    refine ⟨_, (isPadicSymmetricGammaFactor_of_le (by omega)).mp hsym, ?_⟩
    rw [hC τ ωτ hτ hτl hτc _ hsym, multiplicativeConductor_inv, ha', hc_def]
    congr 2
    push_cast
    ring
  -- the gamma certificates of the split twists
  have hG₁' : IsPadicPairGammaFactor F ψ ν.val
      (Langlands.twist ((χ' : F.Carrierˣ →* ℂˣ).comp determinant)
        (Langlands.twist ((ξ : F.Carrierˣ →* ℂˣ).comp determinant) π₁)) σ G₁ := by
    rw [← twist_split F χ ξ π₁]
    exact (isPadicSymmetricGammaFactor_of_le (by omega)).mp hG₁
  have hG₂' : IsPadicPairGammaFactor F ψ ν.val
      (Langlands.twist ((χ' : F.Carrierˣ →* ℂˣ).comp determinant)
        (Langlands.twist ((ξ : F.Carrierˣ →* ℂˣ).comp determinant) π₂)) σ G₂ := by
    rw [← twist_split F χ ξ π₂]
    exact (isPadicSymmetricGammaFactor_of_le (by omega)).mp hG₂
  exact core_gamma_eq F hT1 ψ hψ0 ν.val hf hb hcb hcf hωf hπ₁ξ hπ₂ξ hc₁ hc₂ ℓ₁ hℓ₁ ℓ₂ hℓ₂
    w₁ w₂ hw₁ hw₂ hP hw₁1 hw₂1 hσ hσb ℓ' hℓ' χ' hχb ϖ hϖ f' hκ₁ hsupp hval hequiv C hGall
    hG₁' hG₂'

/-- `HighlyRamifiedGammaStabilityStatement` from the completeness lemma (Jacquet–Shalika 1985,
Lemma (3.2)), the essential-vector level statement, the uniform rank-one statement and the
Kirillov shell input. -/
theorem highlyRamifiedGammaStability_of_inputs
    (hT1 : WhittakerCompletenessStatement.{uF, max uF uV uW})
    (h2 : Conductor.EssentialVectorLevelStatement.{uF, max uF uV uW})
    (h3 : UniformRankOneTwistStatement.{uF, max uF uV uW})
    (hone : UniformRankOneTwistStatement.{uF, uV})
    (hK : KirillovShellInput.{uF, max uF uV uW}) :
    HighlyRamifiedGammaStabilityStatement.{uF, uV, uW} :=
  highlyRamifiedGammaStability_of_adjacentStep h3 hone
    (adjacentStep hT1 (fun n => essentialPairInput h2 h3 n) hK)

end Langlands.RankinSelberg.HighlyRamified
