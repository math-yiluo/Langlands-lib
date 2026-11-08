import Langlands.Representation.RankinSelberg.HighlyRamified.RankOneMonomial
import Langlands.Representation.RankinSelberg.HighlyRamified.InducedLevel

/-!
# Monomial gamma factors of highly ramified twists

Jacquet and Shalika 1985, §4.2 (printed pages 326–327), and its use in (4.4.15)
(printed page 329). Let `σ` be generic of rank `R + 2` with a principal level vector of
level `m'`. For `χ` of large conductor `a`, uniformly in `σ`, every gamma factor of
`(σ ⊗ χ ∘ det, τ)` with `τ` generic of rank `R + 1` and level `f` is
`C X^((R+2)(R+1) a)`, and `C` depends on `τ` only through its central character.

The proof compares `σ` with a generic principal series `σ'` of the same central
character and level, using level-uniform stability of the adjacent pair as a
hypothesis. Multiplicativity writes the gamma factor of `σ'` as a product of
rank-one factors, and `UniformRankOneTwistStatement` evaluates each of them.
-/

noncomputable section

namespace Langlands.RankinSelberg.HighlyRamified

open HarmonicAnalysis Whittaker GeneralLinear

universe uF uV uW uX

variable {p : ℕ} [Fact p.Prime]

/-- The monomial gamma input of the adjacent-rank step (Jacquet and Shalika 1985,
§4.2 and (4.4.15)): for all levels `m'` and `f` there is `A` such that for generic `σ`
of rank `R + 2` with a level-`m'` vector and `χ` with `a(χ) ≥ A`, every gamma factor of
`(σ ⊗ χ ∘ det, τ)` for generic `τ` of rank `R + 1` with a level-`f` vector and central
character `ω` is `C(ω) X^((R+2)(R+1) a(χ))`. -/
def MonomialTwistGamma (R : ℕ) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ),
    F.canonicalTopologicalData.additiveConductor ψ = 0 →
    ∀ m' f : ℕ, ∃ A : ℕ,
      ∀ {W : Type uV} [AddCommGroup W] [Module ℂ W]
        (σ : Representation ℂ (Langlands.GeneralLinear (R + 1 + 1) F.Carrier) W),
        (letI := F.canonicalTopologicalData.topology; Whittaker.IsGeneric ψ (R + 1) σ) →
        HasPrincipalLevelVector F σ m' →
        ∀ χ : (letI := F.canonicalTopologicalData.topology; Quasicharacter F.Carrier),
          A ≤ F.canonicalTopologicalData.multiplicativeConductor χ →
          ∃ C : (F.Carrierˣ →* ℂˣ) → ℂˣ,
            ∀ {X : Type uV} [AddCommGroup X] [Module ℂ X]
              (τ : Representation ℂ (Langlands.GeneralLinear (R + 1) F.Carrier) X)
              (ω : F.Carrierˣ →* ℂˣ),
              (letI := F.canonicalTopologicalData.topology; Whittaker.IsGeneric ψ R τ) →
              HasPrincipalLevelVector F τ f →
              Classification.HasGLCentralCharacter F.Carrier (R + 1) τ ω →
              ∀ G : RationalFunctions,
                IsPadicSymmetricGammaFactor F ψ ν.val
                  (Langlands.twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) σ) τ G →
                G = rationalEpsilonMonomial (C ω)
                  (((R + 1 + 1) * (R + 1) *
                    F.canonicalTopologicalData.multiplicativeConductor χ : ℕ) : ℤ)

section Bounds

variable (F : PadicField.{uF} p)
  (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
  (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ) (R f B : ℕ)

/-- Gamma factors of `(τ ⊗ η ∘ det, 1)` are `c X^((R+1) a(η))` once `a(η) ≥ B`, for
generic `τ` of rank `R + 1` with a level-`f` vector in universe `uX`. -/
def RankOneMonomialBound : Prop :=
  ∀ {X : Type uX} [AddCommGroup X] [Module ℂ X]
    (τ : Representation ℂ (Langlands.GeneralLinear (R + 1) F.Carrier) X),
    (letI := F.canonicalTopologicalData.topology; Whittaker.IsGeneric ψ R τ) →
    HasPrincipalLevelVector F τ f →
    ∀ η : (letI := F.canonicalTopologicalData.topology; Quasicharacter F.Carrier),
      B ≤ F.canonicalTopologicalData.multiplicativeConductor η →
      ∀ G : RationalFunctions,
        IsPadicSymmetricGammaFactor F ψ ν.val
          (Langlands.twist ((η : F.Carrierˣ →* ℂˣ).comp determinant) τ)
          (rankOneCharacter (1 : F.Carrierˣ →* ℂˣ)) G →
        ∃ c : ℂˣ, G = rationalEpsilonMonomial c
          (((R + 1) * F.canonicalTopologicalData.multiplicativeConductor η : ℕ) : ℤ)

/-- Two such `τ` with the same central character have a common gamma factor of
`(τ ⊗ η ∘ det, 1)` once `a(η) ≥ B`. -/
def RankOneCommonBound : Prop :=
  ∀ {X₁ X₂ : Type uX} [AddCommGroup X₁] [Module ℂ X₁] [AddCommGroup X₂] [Module ℂ X₂]
    (τ₁ : Representation ℂ (Langlands.GeneralLinear (R + 1) F.Carrier) X₁)
    (τ₂ : Representation ℂ (Langlands.GeneralLinear (R + 1) F.Carrier) X₂),
    (letI := F.canonicalTopologicalData.topology; Whittaker.IsGeneric ψ R τ₁) →
    (letI := F.canonicalTopologicalData.topology; Whittaker.IsGeneric ψ R τ₂) →
    HasPrincipalLevelVector F τ₁ f → HasPrincipalLevelVector F τ₂ f →
    SameGLCentralCharacter F τ₁ τ₂ →
    ∀ η : (letI := F.canonicalTopologicalData.topology; Quasicharacter F.Carrier),
      B ≤ F.canonicalTopologicalData.multiplicativeConductor η →
      ∃ G : RationalFunctions,
        IsPadicSymmetricGammaFactor F ψ ν.val
          (Langlands.twist ((η : F.Carrierˣ →* ℂˣ).comp determinant) τ₁)
          (rankOneCharacter (1 : F.Carrierˣ →* ℂˣ)) G ∧
        IsPadicSymmetricGammaFactor F ψ ν.val
          (Langlands.twist ((η : F.Carrierˣ →* ℂˣ).comp determinant) τ₂)
          (rankOneCharacter (1 : F.Carrierˣ →* ℂˣ)) G

/-- The induction predicate: for every `χ` with `a(χ) ≥ B`, every gamma factor of
`(I ⊗ χ ∘ det, τ)` against generic `τ` of rank `R + 1` and level `f` is
`c X^((k+1)(R+1) a(χ))`, and two such `τ` with the same central character give the
same gamma factor. -/
def TwistGammaMonomial {k : ℕ} {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (I : Representation ℂ (Langlands.GeneralLinear (k + 1) F.Carrier) W) : Prop :=
  ∀ χ : (letI := F.canonicalTopologicalData.topology; Quasicharacter F.Carrier),
    B ≤ F.canonicalTopologicalData.multiplicativeConductor χ →
    (∀ {X : Type uX} [AddCommGroup X] [Module ℂ X]
      (τ : Representation ℂ (Langlands.GeneralLinear (R + 1) F.Carrier) X),
      (letI := F.canonicalTopologicalData.topology; Whittaker.IsGeneric ψ R τ) →
      HasPrincipalLevelVector F τ f →
      ∀ G : RationalFunctions,
        IsPadicSymmetricGammaFactor F ψ ν.val
          (Langlands.twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) I) τ G →
        ∃ c : ℂˣ, G = rationalEpsilonMonomial c
          (((k + 1) * (R + 1) * F.canonicalTopologicalData.multiplicativeConductor χ : ℕ) : ℤ)) ∧
    (∀ {X₁ X₂ : Type uX} [AddCommGroup X₁] [Module ℂ X₁] [AddCommGroup X₂] [Module ℂ X₂]
      (τ₁ : Representation ℂ (Langlands.GeneralLinear (R + 1) F.Carrier) X₁)
      (τ₂ : Representation ℂ (Langlands.GeneralLinear (R + 1) F.Carrier) X₂),
      (letI := F.canonicalTopologicalData.topology; Whittaker.IsGeneric ψ R τ₁) →
      (letI := F.canonicalTopologicalData.topology; Whittaker.IsGeneric ψ R τ₂) →
      HasPrincipalLevelVector F τ₁ f → HasPrincipalLevelVector F τ₂ f →
      SameGLCentralCharacter F τ₁ τ₂ →
      ∀ G₁ G₂ : RationalFunctions,
        IsPadicSymmetricGammaFactor F ψ ν.val
          (Langlands.twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) I) τ₁ G₁ →
        IsPadicSymmetricGammaFactor F ψ ν.val
          (Langlands.twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) I) τ₂ G₂ →
        G₁ = G₂)

end Bounds

/-- If `a(ρ) < a(χ)`, then `a(ρ χ) = a(χ)`. -/
theorem multiplicativeConductor_mul_of_lt (F : PadicField.{uF} p)
    (χ ρ : letI := F.canonicalTopologicalData.topology; Quasicharacter F.Carrier)
    (h : F.canonicalTopologicalData.multiplicativeConductor ρ <
      F.canonicalTopologicalData.multiplicativeConductor χ) :
    F.canonicalTopologicalData.multiplicativeConductor (ρ * χ) =
      F.canonicalTopologicalData.multiplicativeConductor χ := by
  apply le_antisymm _ (le_multiplicativeConductor_mul F χ ρ h)
  apply (F.canonicalTopologicalData.multiplicativeTrivialAt_iff_conductor_le _ _).mp
  intro u hu
  have h1 := (F.canonicalTopologicalData.multiplicativeTrivialAt_iff_conductor_le ρ _).mpr
    h.le u hu
  have h2 := F.canonicalTopologicalData.multiplicativeConductor_spec χ u hu
  change ρ u * χ u = 1
  rw [h1, h2, one_mul]

/-- The twist of the rank-one character `ρ ∘ det` by `χ ∘ det` is `(ρ χ) ∘ det`. -/
def rankOneExtensionCharacterTwistEquiv (F : PadicField.{uF} p)
    (ρ χ : letI := F.canonicalTopologicalData.topology; Quasicharacter F.Carrier) :
    (Langlands.twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant)
      (rankOneExtensionCharacter.{uF, uW} F ρ)).Equiv
      (rankOneCharacter (((ρ * χ : letI := F.canonicalTopologicalData.topology
        Quasicharacter F.Carrier)) : F.Carrierˣ →* ℂˣ)) :=
  Representation.Equiv.mk (ULift.moduleEquiv : ULift.{uW} ℂ ≃ₗ[ℂ] ℂ) fun g => by
    apply LinearMap.ext
    intro v
    change ((χ (determinant g) : ℂˣ) : ℂ) • (((ρ (determinant g) : ℂˣ) : ℂ) • v.down) =
      ((ρ (determinant g) * χ (determinant g) : ℂˣ) : ℂ) • v.down
    rw [smul_smul, Units.val_mul, mul_comm]

/-- The rank-one base case: for `a(ρ) < B`, the rank-one representation `ρ ∘ det`
satisfies `TwistGammaMonomial`. -/
theorem twistGammaMonomial_rankOneExtensionCharacter (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ) {R f B : ℕ}
    (hmono : RankOneMonomialBound.{uF, uX} F ψ ν R f B)
    (hcommon : RankOneCommonBound.{uF, uX} F ψ ν R f B)
    (ρ : letI := F.canonicalTopologicalData.topology; Quasicharacter F.Carrier)
    (hρ : F.canonicalTopologicalData.multiplicativeConductor ρ < B) :
    TwistGammaMonomial.{uF, uW, uX} F ψ ν R f B (k := 0)
      (rankOneExtensionCharacter.{uF, uW} F ρ) := by
  let := F.canonicalTopologicalData.topology
  intro χ hχ
  have hρχ := multiplicativeConductor_mul_of_lt F χ ρ (lt_of_lt_of_le hρ hχ)
  have hB : B ≤ F.canonicalTopologicalData.multiplicativeConductor (ρ * χ) := hρχ ▸ hχ
  -- Convert a gamma factor of `(ρ ∘ det ⊗ χ ∘ det, τ)` to one of `(τ ⊗ (ρ χ) ∘ det, 1)`.
  have conv : ∀ {X : Type uX} [AddCommGroup X] [Module ℂ X]
      (τ : Representation ℂ (Langlands.GeneralLinear (R + 1) F.Carrier) X),
      Whittaker.IsGeneric ψ R τ → ∀ G : RationalFunctions,
      IsPadicSymmetricGammaFactor F ψ ν.val
        (Langlands.twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant)
          (rankOneExtensionCharacter.{uF, uW} F ρ)) τ G →
      IsPadicSymmetricGammaFactor F ψ ν.val
        (Langlands.twist (((ρ * χ : Quasicharacter F.Carrier) : F.Carrierˣ →* ℂˣ).comp
          determinant) τ) (rankOneCharacter (1 : F.Carrierˣ →* ℂˣ)) G := by
    intro X _ _ τ hτ G hG
    have hτw := isOfWhittakerType_of_isGeneric F hτ
    have h0 := (IsPadicSymmetricGammaFactor.congr_equiv
      (rankOneExtensionCharacterTwistEquiv F ρ χ) (Representation.Equiv.refl τ)).mp hG
    have h2 := (isPadicSymmetricGammaFactor_rankOne_test_twist ψ ν.val (ρ * χ) τ
      (fun _ => hτw) G).mpr h0
    exact (Padic.isPadicSymmetricGammaFactor_comm F ψ ν.val _ _
      (rankOneCharacter_isOfWhittakerType p F ψ 1)
      (isOfWhittakerType_of_isGeneric F
        (isGeneric_quasicharacter_twist F.canonicalTopologicalData ψ (ρ * χ) hτ)) G).mp h2
  refine ⟨fun τ hτ hf G hG => ?_, fun τ₁ τ₂ hτ₁ hτ₂ hf₁ hf₂ hc G₁ G₂ hG₁ hG₂ => ?_⟩
  · obtain ⟨c, hc⟩ := hmono τ hτ hf (ρ * χ) hB G (conv τ hτ G hG)
    refine ⟨c, hc.trans ?_⟩
    rw [hρχ, zero_add, one_mul]
  · obtain ⟨G, h₁, h₂⟩ := hcommon τ₁ τ₂ hτ₁ hτ₂ hf₁ hf₂ hc (ρ * χ) hB
    exact ((conv τ₁ hτ₁ G₁ hG₁).unique h₁).trans ((conv τ₂ hτ₂ G₂ hG₂).unique h₂).symm

/-- Epsilon monomials multiply by multiplying constants and adding exponents. -/
theorem rationalEpsilonMonomial_mul_coe (c c' : ℂˣ) (m m' : ℤ) :
    (rationalEpsilonMonomial c m : RationalFunctions) * rationalEpsilonMonomial c' m' =
      rationalEpsilonMonomial (c * c') (m + m') := by
  rw [← Units.val_mul]
  congr 1
  simp only [rationalEpsilonMonomial, map_mul, zpow_add]
  exact mul_mul_mul_comm _ _ _ _

section Canonical

local instance monomialGammaNormedField (F : PadicField.{uF} p) :
    NontriviallyNormedField F.Carrier :=
  F.canonicalNormedField

/-- Multiplicativity for a twisted pair induction `(A × C) ⊗ χ ∘ det` against a test
`τ`: its gamma factor is the product of the gamma factors of `τ` against `A ⊗ χ ∘ det`
and `C ⊗ χ ∘ det`. -/
theorem exists_gammaFactor_twist_pairInduced (F : PadicField.{uF} p)
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    {r t : ℕ} {X : Type uX} [AddCommGroup X] [Module ℂ X]
    (τ : Representation ℂ (Langlands.GeneralLinear (t + 1) F.Carrier) X)
    (hτ : Whittaker.IsGeneric ψ t τ) (χ : Quasicharacter F.Carrier)
    (A : SmoothRep.{0, uF, uW} ℂ (Langlands.GeneralLinear (r + 1) F.Carrier))
    (C : SmoothRep.{0, uF, uW} ℂ (Langlands.GeneralLinear 1 F.Carrier))
    (hA : Whittaker.IsGeneric ψ r A.representation)
    (hC : Whittaker.IsGeneric ψ 0 C.representation)
    (hAC : Whittaker.IsGeneric ψ (r + 1) (pairInduced F A C)) :
    ∃ H : Fin 2 → RationalFunctions,
      IsPadicSymmetricGammaFactor F ψ ν.val τ
        (twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) A.representation) (H 0) ∧
      IsPadicSymmetricGammaFactor F ψ ν.val τ
        (twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) C.representation) (H 1) ∧
      IsPadicSymmetricGammaFactor F ψ ν.val
        (twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) (pairInduced F A C)) τ
        (H 0 * H 1) := by
  let T := F.canonicalTopologicalData
  have hτw := isOfWhittakerType_of_isGeneric F hτ
  have hblocks : ∀ i, IsOfWhittakerType (pairSizes r i) (standardCharacter ψ (pairSizes r i))
      (twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) (pairFamily F A C i).representation) :=
    Fin.forall_fin_two.mpr
      ⟨isOfWhittakerType_of_isGeneric F (isGeneric_quasicharacter_twist T ψ χ hA),
        isOfWhittakerType_of_isGeneric F (isGeneric_quasicharacter_twist T ψ χ hC)⟩
  obtain ⟨H, hH, hP⟩ := gammaMultiplicativity p F ψ ν t (r + 1) 2 (pairSizes r)
    (pairSizes_sum r) τ
    (fun i => twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant)
      (pairFamily F A C i).representation) hτw hblocks
  refine ⟨H, hH 0, hH 1, ?_⟩
  have e := T.normalizedProductDeterminantTwistEquiv
    (succBlockShape (pairSizes r) (pairSizes_sum r)) (quasicharacterSmoothCharacter T χ)
    (fun i => (pairFamily F A C i).representation)
  have hP' := (IsPadicSymmetricGammaFactor.congr_equiv (Representation.Equiv.refl τ)
    e.symm).mp hP
  rw [Fin.prod_univ_two] at hP'
  exact (Padic.isPadicSymmetricGammaFactor_comm F ψ ν.val τ _ hτw
    (isOfWhittakerType_of_isGeneric F (isGeneric_quasicharacter_twist T ψ χ hAC)) _).mp hP'

/-- The induction step: if `A` and `C` satisfy `TwistGammaMonomial` and `A × C` is
generic, then `A × C` satisfies it, with exponents added. -/
theorem twistGammaMonomial_pairInduced (F : PadicField.{uF} p)
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ) {R f B k : ℕ}
    (A : SmoothRep.{0, uF, uW} ℂ (Langlands.GeneralLinear (k + 1) F.Carrier))
    (C : SmoothRep.{0, uF, uW} ℂ (Langlands.GeneralLinear 1 F.Carrier))
    (hA : Whittaker.IsGeneric ψ k A.representation)
    (hC : Whittaker.IsGeneric ψ 0 C.representation)
    (hAC : Whittaker.IsGeneric ψ (k + 1) (pairInduced F A C))
    (hgA : TwistGammaMonomial.{uF, uW, uX} F ψ ν R f B A.representation)
    (hgC : TwistGammaMonomial.{uF, uW, uX} F ψ ν R f B (k := 0) C.representation) :
    TwistGammaMonomial.{uF, max uF uW, uX} F ψ ν R f B (k := k + 1) (pairInduced F A C) := by
  let T := F.canonicalTopologicalData
  intro χ hχ
  obtain ⟨hMA, hSA⟩ := hgA χ hχ
  obtain ⟨hMC, hSC⟩ := hgC χ hχ
  have fact : ∀ {X : Type uX} [AddCommGroup X] [Module ℂ X]
      (τ : Representation ℂ (Langlands.GeneralLinear (R + 1) F.Carrier) X),
      Whittaker.IsGeneric ψ R τ → ∃ H : Fin 2 → RationalFunctions,
        IsPadicSymmetricGammaFactor F ψ ν.val
          (twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) A.representation) τ (H 0) ∧
        IsPadicSymmetricGammaFactor F ψ ν.val
          (twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) C.representation) τ (H 1) ∧
        IsPadicSymmetricGammaFactor F ψ ν.val
          (twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) (pairInduced F A C)) τ
          (H 0 * H 1) := by
    intro X _ _ τ hτ
    obtain ⟨H, h0, h1, h2⟩ := exists_gammaFactor_twist_pairInduced F ψ ν τ hτ χ A C hA hC hAC
    have hτw := isOfWhittakerType_of_isGeneric F hτ
    exact ⟨H, (Padic.isPadicSymmetricGammaFactor_comm F ψ ν.val τ _ hτw
        (isOfWhittakerType_of_isGeneric F (isGeneric_quasicharacter_twist T ψ χ hA)) _).mp h0,
      (Padic.isPadicSymmetricGammaFactor_comm F ψ ν.val τ _ hτw
        (isOfWhittakerType_of_isGeneric F (isGeneric_quasicharacter_twist T ψ χ hC)) _).mp h1,
      h2⟩
  refine ⟨fun τ hτ hf G hG => ?_, fun τ₁ τ₂ hτ₁ hτ₂ hf₁ hf₂ hc G₁ G₂ hG₁ hG₂ => ?_⟩
  · obtain ⟨H, h0, h1, h2⟩ := fact τ hτ
    obtain ⟨c₀, hc₀⟩ := hMA τ hτ hf _ h0
    obtain ⟨c₁, hc₁⟩ := hMC τ hτ hf _ h1
    refine ⟨c₀ * c₁, ?_⟩
    rw [hG.unique h2, hc₀, hc₁, rationalEpsilonMonomial_mul_coe]
    congr 2
    push_cast
    ring
  · obtain ⟨H, h0, h1, h2⟩ := fact τ₁ hτ₁
    obtain ⟨H', h0', h1', h2'⟩ := fact τ₂ hτ₂
    rw [hG₁.unique h2, hG₂.unique h2', hSA τ₁ τ₂ hτ₁ hτ₂ hf₁ hf₂ hc _ _ h0 h0',
      hSC τ₁ τ₂ hτ₁ hτ₂ hf₁ hf₂ hc _ _ h1 h1']

end Canonical

/-- `TwistGammaMonomial` is unchanged by a twist with an unramified character, since
`a(χ μ) = a(χ)` for unramified `μ`. -/
theorem twistGammaMonomial_twist_unramified (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ) {R f B k : ℕ}
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (I : Representation ℂ (Langlands.GeneralLinear (k + 1) F.Carrier) W) (y : ℂˣ)
    (h : TwistGammaMonomial.{uF, uW, uX} F ψ ν R f B I) :
    TwistGammaMonomial.{uF, uW, uX} F ψ ν R f B
      (Langlands.twist (((F.canonicalTopologicalData.unramifiedCharacterContinuous y :
        letI := F.canonicalTopologicalData.topology; Quasicharacter F.Carrier) :
          F.Carrierˣ →* ℂˣ).comp determinant) I) := by
  let := F.canonicalTopologicalData.topology
  intro χ hχ
  let μ : Quasicharacter F.Carrier := F.canonicalTopologicalData.unramifiedCharacterContinuous y
  have hμ : F.canonicalTopologicalData.IsUnramifiedQuasicharacter μ :=
    (F.canonicalTopologicalData.multiplicativeConductor_eq_zero_iff μ).mp
      (multiplicativeConductor_unramifiedCharacter F y)
  have hconv : F.canonicalTopologicalData.multiplicativeConductor (χ * μ) =
      F.canonicalTopologicalData.multiplicativeConductor χ :=
    F.canonicalTopologicalData.multiplicativeConductor_mul_unramified χ μ hμ
  obtain ⟨hM, hS⟩ := h (χ * μ) (hconv.symm ▸ hχ)
  have htw : Langlands.twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant)
      (Langlands.twist ((μ : F.Carrierˣ →* ℂˣ).comp determinant) I) =
      Langlands.twist (((χ * μ : Quasicharacter F.Carrier) : F.Carrierˣ →* ℂˣ).comp
        determinant) I := by
    rw [twist_twist]
    rfl
  refine ⟨fun τ hτ hf G hG => ?_, fun τ₁ τ₂ hτ₁ hτ₂ hf₁ hf₂ hc G₁ G₂ hG₁ hG₂ => ?_⟩
  · rw [htw] at hG
    obtain ⟨c, hc⟩ := hM τ hτ hf G hG
    exact ⟨c, hc.trans (by rw [hconv])⟩
  · rw [htw] at hG₁ hG₂
    exact hS τ₁ τ₂ hτ₁ hτ₂ hf₁ hf₂ hc G₁ G₂ hG₁ hG₂

section Construction

local instance monomialGammaConstructionNormedField (F : PadicField.{uF} p) :
    NontriviallyNormedField F.Carrier :=
  F.canonicalNormedField

/-- The rank-one representation `ρ ∘ det` is generic. -/
theorem isGeneric_rankOneExtensionCharacter (F : PadicField.{uF} p)
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ρ : Quasicharacter F.Carrier) :
    Whittaker.IsGeneric ψ 0 (rankOneExtensionCharacter.{uF, uW} F ρ) := by
  have := Classification.UnlinkedSegmentSocleProductIrreducibleProof.isIrreducible_of_finrank_eq_one
    (rankOneExtensionCharacter.{uF, uW} F ρ) finrank_ulift_complex
  exact Whittaker.isGeneric_rankOne ψ _ (rankOneExtensionCharacter_isOfWhittakerType.{uF, uW} F ψ ρ).1

/-- The rank-one representation `ρ ∘ det` has central character `ρ`. -/
theorem hasGLCentralCharacter_rankOneExtensionCharacter (F : PadicField.{uF} p)
    (ρ : Quasicharacter F.Carrier) :
    Classification.HasGLCentralCharacter F.Carrier 1 (rankOneExtensionCharacter.{uF, uW} F ρ)
      (ρ : F.Carrierˣ →* ℂˣ) := by
  intro c v
  apply ULift.ext
  change ((ρ (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 1) c)) :
    ℂˣ) : ℂ) • v.down = ((ρ c : ℂˣ) : ℂ) • v.down
  rw [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, pow_one]

/-- Unramified characters multiply by multiplying their parameters. -/
theorem unramifiedCharacter_mul (F : PadicField.{uF} p) (w z : ℂˣ) :
    F.canonicalTopologicalData.unramifiedCharacter (w * z) =
      F.canonicalTopologicalData.unramifiedCharacter w *
        F.canonicalTopologicalData.unramifiedCharacter z := by
  ext u
  simp [PadicField.TopologicalData.unramifiedCharacter_apply]

/-- Iterated induction `ρ × μ_{z_1} × ⋯ × μ_{z_n}` with every step generic: a generic
representation of rank `n + 1` with a level-`m'` vector, central character `ρ μ_w` for
some `w`, satisfying `TwistGammaMonomial`. -/
theorem exists_iteratedPrincipalSeries (F : PadicField.{uF} p)
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ) {R f B m' : ℕ}
    (hmono : RankOneMonomialBound.{uF, uX} F ψ ν R f B)
    (hcommon : RankOneCommonBound.{uF, uX} F ψ ν R f B)
    (ρ : Quasicharacter F.Carrier)
    (hρB : F.canonicalTopologicalData.multiplicativeConductor ρ < B)
    (hρm : F.canonicalTopologicalData.multiplicativeConductor ρ ≤ m') (n : ℕ) :
    ∃ (I : SmoothRep.{0, uF, max uF uW} ℂ (Langlands.GeneralLinear (n + 1) F.Carrier))
      (w : ℂˣ),
      Whittaker.IsGeneric ψ n I.representation ∧
      HasPrincipalLevelVector F I.representation m' ∧
      Classification.HasGLCentralCharacter F.Carrier (n + 1) I.representation
        ((ρ : F.Carrierˣ →* ℂˣ) * F.canonicalTopologicalData.unramifiedCharacter w) ∧
      TwistGammaMonomial.{uF, max uF uW, uX} F ψ ν R f B I.representation := by
  let T := F.canonicalTopologicalData
  have := infinite_units_complex
  induction n with
  | zero =>
    refine ⟨SmoothRep.of (rankOneExtensionCharacter.{uF, max uF uW} F ρ)
        (rankOneExtensionCharacter_isSmooth F ψ ρ), 1,
      isGeneric_rankOneExtensionCharacter F ψ ρ,
      hasPrincipalLevelVector_rankOneExtensionCharacter F ρ hρm, ?_,
      twistGammaMonomial_rankOneExtensionCharacter F ψ ν hmono hcommon ρ hρB⟩
    intro c v
    refine (hasGLCentralCharacter_rankOneExtensionCharacter.{uF, max uF uW} F ρ c v).trans ?_
    have h1 : ((ρ : F.Carrierˣ →* ℂˣ) * T.unramifiedCharacter 1) c = ρ c := by
      simp
    exact congrArg (fun x : ℂˣ => (x : ℂ) • v) h1.symm
  | succ n ih =>
    obtain ⟨I, w, hIg, hIm, hIc, hIgood⟩ := ih
    obtain ⟨z, hz⟩ := (pairInductionGenericity.{uF, max uF uW} p F ψ n I hIg).exists_notMem
    have hIz : Whittaker.IsGeneric ψ (n + 1)
        (pairInduced F I (unramifiedRankOne.{uF, max uF uW} F z)) := not_not.mp hz
    have hμ := isGeneric_unramifiedRankOne.{uF, max uF uW} F ψ z
    have hμa : T.multiplicativeConductor (T.unramifiedCharacterContinuous z) = 0 :=
      multiplicativeConductor_unramifiedCharacter F z
    have hμgood : TwistGammaMonomial.{uF, max uF uW, uX} F ψ ν R f B (k := 0)
        (unramifiedRankOne.{uF, max uF uW} F z).representation :=
      twistGammaMonomial_rankOneExtensionCharacter F ψ ν hmono hcommon
        (T.unramifiedCharacterContinuous z) (hμa ▸ lt_of_le_of_lt (Nat.zero_le _) hρB)
    have hμm : HasPrincipalLevelVector F (unramifiedRankOne.{uF, max uF uW} F z).representation
        m' :=
      hasPrincipalLevelVector_rankOneExtensionCharacter F (T.unramifiedCharacterContinuous z)
        (hμa ▸ Nat.zero_le m')
    refine ⟨SmoothRep.of (pairInduced F I (unramifiedRankOne.{uF, max uF uW} F z))
        hIz.2.1.1, w * z, hIz, ?_, ?_,
      twistGammaMonomial_pairInduced F ψ ν I _ hIg hμ hIz hIgood hμgood⟩
    · exact hasPrincipalLevelVector_normalizedProductInduced F (pairSizes_sum n)
        (fun i => (pairFamily F I (unramifiedRankOne.{uF, max uF uW} F z) i).representation)
        (Fin.forall_fin_two.mpr ⟨hIm, hμm⟩)
    · let c : Fin 2 → (F.Carrierˣ →* ℂˣ) :=
        ![(ρ : F.Carrierˣ →* ℂˣ) * T.unramifiedCharacter w,
          ((T.unramifiedCharacter z).comp (determinant (n := 1))).comp
            (GeneralLinear.scalar (n := 1))]
      have hblocks : ∀ i, Classification.HasScalarCharacter
          (pairFamily F I (unramifiedRankOne.{uF, max uF uW} F z) i).representation
          GeneralLinear.scalar (c i) :=
        Fin.forall_fin_two.mpr ⟨hIc, hasScalarCharacter_unramifiedRankOne.{uF, max uF uW} F z⟩
      have hprod : ∏ i, c i = (ρ : F.Carrierˣ →* ℂˣ) * T.unramifiedCharacter (w * z) := by
        ext u
        simp [c, Fin.prod_univ_two, PadicField.TopologicalData.unramifiedCharacter_apply,
          Matrix.GeneralLinearGroup.det_scalar, mul_assoc]
      have h : Classification.HasScalarCharacter
          (pairInduced F I (unramifiedRankOne.{uF, max uF uW} F z)) GeneralLinear.scalar
          (∏ i, c i) :=
        T.hasScalarCharacter_normalizedProductInduced
          (succBlockShape (pairSizes n) (pairSizes_sum n)) hblocks
      rw [hprod] at h
      exact h

/-- The comparison representation: a generic representation of rank `R + 2` with a
level-`m'` vector and central character exactly `ω`, satisfying `TwistGammaMonomial`.
It is the iterated principal series of `exists_iteratedPrincipalSeries`, twisted by an
unramified character `μ_y` with `y^(R+2) = w⁻¹`. -/
theorem exists_principalSeries (F : PadicField.{uF} p)
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ) {R f B m' : ℕ}
    (hmono : RankOneMonomialBound.{uF, uX} F ψ ν R f B)
    (hcommon : RankOneCommonBound.{uF, uX} F ψ ν R f B)
    (ω : Quasicharacter F.Carrier)
    (hωB : F.canonicalTopologicalData.multiplicativeConductor ω < B)
    (hωm : F.canonicalTopologicalData.multiplicativeConductor ω ≤ m') :
    ∃ (W : Type (max uF uW)) (_ : AddCommGroup W) (_ : Module ℂ W)
      (σ : Representation ℂ (Langlands.GeneralLinear (R + 1 + 1) F.Carrier) W),
      Whittaker.IsGeneric ψ (R + 1) σ ∧ HasPrincipalLevelVector F σ m' ∧
      Classification.HasGLCentralCharacter F.Carrier (R + 1 + 1) σ (ω : F.Carrierˣ →* ℂˣ) ∧
      TwistGammaMonomial.{uF, max uF uW, uX} F ψ ν R f B σ := by
  let T := F.canonicalTopologicalData
  obtain ⟨I, w, hIg, hIm, hIc, hIgood⟩ :=
    exists_iteratedPrincipalSeries.{uF, uW, uX} F ψ ν hmono hcommon ω hωB hωm (R + 1)
  obtain ⟨y₀, hy₀⟩ := IsAlgClosed.exists_pow_nat_eq ((w⁻¹ : ℂˣ) : ℂ) (Nat.succ_pos (R + 1))
  have hy0 : y₀ ≠ 0 := by
    rintro rfl
    rw [zero_pow (Nat.succ_ne_zero _)] at hy₀
    exact (w⁻¹).ne_zero hy₀.symm
  let y : ℂˣ := Units.mk0 y₀ hy0
  have hy : y ^ (R + 1 + 1) = w⁻¹ := Units.ext (by simpa [y] using hy₀)
  refine ⟨_, _, _, Langlands.twist
    (((T.unramifiedCharacterContinuous y : Quasicharacter F.Carrier) :
      F.Carrierˣ →* ℂˣ).comp determinant) I.representation,
    isGeneric_quasicharacter_twist T ψ (T.unramifiedCharacterContinuous y) hIg,
    hasPrincipalLevelVector_twist_unramified F I.representation y hIm, ?_,
    twistGammaMonomial_twist_unramified F ψ ν I.representation y hIgood⟩
  have h := hasGLCentralCharacter_twist
    ((T.unramifiedCharacterContinuous y : Quasicharacter F.Carrier) : F.Carrierˣ →* ℂˣ) hIc
  have hchar : (ω : F.Carrierˣ →* ℂˣ) * T.unramifiedCharacter w *
      ((T.unramifiedCharacterContinuous y : Quasicharacter F.Carrier) :
        F.Carrierˣ →* ℂˣ) ^ (R + 1 + 1) = (ω : F.Carrierˣ →* ℂˣ) := by
    ext u
    change ((ω u * T.unramifiedCharacter w u * (T.unramifiedCharacter y u) ^ (R + 1 + 1) :
      ℂˣ) : ℂ) = ((ω u : ℂˣ) : ℂ)
    congr 1
    rw [PadicField.TopologicalData.unramifiedCharacter_apply,
      PadicField.TopologicalData.unramifiedCharacter_apply, ← zpow_natCast, ← zpow_mul,
      mul_comm (T.ord (u : F.Carrier)), zpow_mul, zpow_natCast, hy, inv_zpow, mul_assoc,
      mul_inv_cancel, mul_one]
  rw [hchar] at h
  exact h

/-- Jacquet and Shalika 1985, §4.2 and (4.4.15): `UniformRankOneTwistStatement` and
level-uniform stability of the adjacent pair `(R + 2, R + 1)` give
`MonomialTwistGamma R`, with all spaces in the universe `max uF uV`. -/
theorem monomialTwistGamma (h3 : UniformRankOneTwistStatement.{uF, max uF uV}) {R : ℕ}
    (hIH : UniformPairStability.{uF, max uF uV, max uF uV} (R + 1) R) :
    MonomialTwistGamma.{uF, max uF uV} R := by
  intro p _ F ψ ν hψ m' f
  let T := F.canonicalTopologicalData
  obtain ⟨B₁, hB₁⟩ := exists_bound_rankOne_gammaMonomial h3 F ψ ν hψ R f
  obtain ⟨B₂, -, hB₂⟩ := h3 p F ψ ν hψ R f
  obtain ⟨A₀, hA₀⟩ := hIH p F ψ ν hψ m' f
  let B := max (max B₁ B₂) (m' + 1)
  have hmono : RankOneMonomialBound.{uF, max uF uV} F ψ ν R f B :=
    fun τ hτ hf η hη => hB₁ τ hτ hf η
      ((le_max_left B₁ B₂).trans ((le_max_left _ (m' + 1)).trans hη))
  have hcommon : RankOneCommonBound.{uF, max uF uV} F ψ ν R f B :=
    fun τ₁ τ₂ h₁ h₂ hf₁ hf₂ hc η hη => hB₂ τ₁ τ₂ h₁ h₂ hf₁ hf₂ hc η
      ((le_max_right B₁ B₂).trans ((le_max_left _ (m' + 1)).trans hη))
  refine ⟨max A₀ B, ?_⟩
  intro W _ _ σ hσ hσm χ hχ
  obtain ⟨ω, hω⟩ := exists_quasicharacter_hasGLCentralCharacter F ψ σ hσ
  have haω := multiplicativeConductor_le_of_hasGLCentralCharacter F σ ω hω hσm
  obtain ⟨W', _, _, σ', hσ'g, hσ'm, hσ'c, hσ'good⟩ :=
    exists_principalSeries.{uF, uV, max uF uV} F ψ ν hmono hcommon ω
      (lt_of_le_of_lt haω (Nat.lt_of_succ_le (le_max_right _ _))) haω
  have hχB : B ≤ T.multiplicativeConductor χ := (le_max_right _ _).trans hχ
  have hχA : A₀ ≤ T.multiplicativeConductor χ := (le_max_left _ _).trans hχ
  obtain ⟨hM, hS⟩ := hσ'good χ hχB
  have hσ'χ := isGeneric_quasicharacter_twist T ψ χ hσ'g
  have key : ∀ ω' : F.Carrierˣ →* ℂˣ, ∃ c : ℂˣ,
      ∀ {X : Type (max uF uV)} [AddCommGroup X] [Module ℂ X]
        (τ : Representation ℂ (Langlands.GeneralLinear (R + 1) F.Carrier) X),
        Whittaker.IsGeneric ψ R τ → HasPrincipalLevelVector F τ f →
        Classification.HasGLCentralCharacter F.Carrier (R + 1) τ ω' →
        ∀ G : RationalFunctions,
          IsPadicSymmetricGammaFactor F ψ ν.val
            (Langlands.twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) σ) τ G →
          G = rationalEpsilonMonomial c
            (((R + 1 + 1) * (R + 1) * T.multiplicativeConductor χ : ℕ) : ℤ) := by
    intro ω'
    by_cases hex : ∃ (X : Type (max uF uV)) (_ : AddCommGroup X) (_ : Module ℂ X)
        (τ₀ : Representation ℂ (Langlands.GeneralLinear (R + 1) F.Carrier) X),
        Whittaker.IsGeneric ψ R τ₀ ∧ HasPrincipalLevelVector F τ₀ f ∧
          Classification.HasGLCentralCharacter F.Carrier (R + 1) τ₀ ω'
    · obtain ⟨X₀, _, _, τ₀, h₀, hf₀, hω₀⟩ := hex
      have hG₀ := genericSymmetricGammaFactor_isPadic F ψ ν.val ν.property _ τ₀ hσ'χ h₀
      obtain ⟨c, hc⟩ := hM τ₀ h₀ hf₀ _ hG₀
      refine ⟨c, fun τ hτ hf hω'' G hG => ?_⟩
      have hG' := genericSymmetricGammaFactor_isPadic F ψ ν.val ν.property _ τ hσ'χ hτ
      have e₁ := hA₀ σ σ' τ hσ hσ'g hτ hσm hσ'm hf ⟨ω, hω, hσ'c⟩ χ hχA G _ hG hG'
      have e₂ := hS τ τ₀ hτ h₀ hf hf₀ ⟨ω', hω'', hω₀⟩ _ _ hG' hG₀
      rw [e₁, e₂, hc]
    · exact ⟨1, fun τ hτ hf hω'' => absurd ⟨_, _, _, τ, hτ, hf, hω''⟩ hex⟩
  choose C hC using key
  exact ⟨C, fun τ ω' hτ hf hω' G hG => hC ω' τ hτ hf hω' G hG⟩

end Construction

end Langlands.RankinSelberg.HighlyRamified
