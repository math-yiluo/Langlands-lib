import Langlands.Representation.RankinSelberg.GammaFactor

noncomputable section

namespace Langlands.Whittaker

universe uG uV uV₂

variable {G : Type uG} [Group G] {N : Subgroup G} {θ : N →* ℂˣ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {V₂ : Type uV₂} [AddCommGroup V₂] [Module ℂ V₂]
  {π : Representation ℂ G V} {π₂ : Representation ℂ G V₂}
  {ℓ : functionals N θ π} {ℓ₂ : functionals N θ π₂}

/-- The actual intertwiner between nested coefficient images. It preserves the
underlying equivariant function, even when the original carriers differ. -/
def coefficientModelInclusionMap (hM : coefficientModel π ℓ ≤ coefficientModel π₂ ℓ₂) :
    (modelRepresentation π ℓ).IntertwiningMap (modelRepresentation π₂ ℓ₂) where
  toLinearMap := Submodule.inclusion hM
  isIntertwining' _ := rfl

@[simp]
theorem coefficientModelInclusionMap_val
    (hM : coefficientModel π ℓ ≤ coefficientModel π₂ ℓ₂)
    (f : (coefficientModel π ℓ).toSubmodule) :
    (coefficientModelInclusionMap hM f).val = f.val := rfl

theorem coefficientModelInclusionMap_injective
    (hM : coefficientModel π ℓ ≤ coefficientModel π₂ ℓ₂) :
    Function.Injective (coefficientModelInclusionMap hM) := by
  intro f g h
  exact Subtype.ext (congrArg (fun f₂ : (coefficientModel π₂ ℓ₂).toSubmodule => f₂.val) h)

end Langlands.Whittaker

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration Polynomial

universe uF uV uW uV₂ uW₂

section EqualRank

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [MeasurableSpace F] {n : ℕ} [MeasurableSpace (LeftUnipotentQuotient n F)]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {V₂ : Type uV₂} [AddCommGroup V₂] [Module ℂ V₂]
  {W₂ : Type uW₂} [AddCommGroup W₂] [Module ℂ W₂]
  {q : ℕ} {ψ : UnitaryAdditiveCharacter F} {abv : AbsoluteValue F ℝ}
  {μ : Measure (LeftUnipotentQuotient n F)} {ν : AdditiveHaarMeasure F}
  {π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V}
  {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W}
  {π₂ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V₂}
  {σ₂ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W₂}
  {ℓ : glFunctionals ψ n π} {ℓ' : glInverseFunctionals ψ n σ}
  {ℓ₂ : glFunctionals ψ n π₂} {ℓ₂' : glInverseFunctionals ψ n σ₂}

/-- Two existing fixed-functional gamma equations on nested coefficient models
have the same factor. Nonvanishing comes from the smaller model. -/
theorem EqualRankGammaEquation.eq_of_model_le (hq : 1 < q) (hℓ' : ℓ'.val ≠ 0)
    (hM : coefficientModel π ℓ ≤ coefficientModel π₂ ℓ₂)
    (hM' : coefficientModel σ ℓ' ≤ coefficientModel σ₂ ℓ₂')
    {G G₂ : RationalFunctions}
    (h : EqualRankGammaEquation q ψ abv μ ν π σ ℓ ℓ' G)
    (h₂ : EqualRankGammaEquation q ψ abv μ ν π₂ σ₂ ℓ₂ ℓ₂' G₂) : G = G₂ := by
  obtain ⟨ζ, hζ, ⟨R, ⟨f, f', Φ, hR⟩, hR0⟩, hFE⟩ := h
  obtain ⟨ζ₂, hζ₂, -, hFE₂⟩ := h₂
  have hζ₂small : HasModelMinusOneScalar σ ℓ' ζ₂ :=
    fun f' g => hζ₂ (coefficientModelInclusionMap hM' f') g
  obtain rfl := HasModelMinusOneScalar.unique hℓ' hζ hζ₂small
  obtain ⟨Φhat, R₁, Rd₁, hΦ₁, hR₁, hRd₁, hN₁⟩ := hFE f f' Φ
  obtain ⟨Φhat₂, R₂, Rd₂, hΦ₂, hR₂, hRd₂, hN₂⟩ :=
    hFE₂ (coefficientModelInclusionMap hM f) (coefficientModelInclusionMap hM' f') Φ
  obtain rfl := hΦ₁.unique hΦ₂
  obtain rfl := hR.unique hq hR₁
  obtain rfl := hR.unique hq hR₂
  obtain rfl := hRd₁.unique hq hRd₂
  exact hN₁.gamma_unique hq hR0 hN₂

end EqualRank

section UnequalRank

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [MeasurableSpace F] {n r : ℕ} [MeasurableSpace (LeftUnipotentQuotient n F)]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {V₂ : Type uV₂} [AddCommGroup V₂] [Module ℂ V₂]
  {W₂ : Type uW₂} [AddCommGroup W₂] [Module ℂ W₂]
  {hnr : n < r} {q : ℕ} {ψ : UnitaryAdditiveCharacter F} {abv : AbsoluteValue F ℝ}
  {μ : Measure (LeftUnipotentQuotient n F)} {ν : AdditiveHaarMeasure F}
  {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V}
  {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W}
  {π₂ : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V₂}
  {σ₂ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W₂}
  {ℓ : glFunctionals ψ r π} {ℓ' : glInverseFunctionals ψ n σ}
  {ℓ₂ : glFunctionals ψ r π₂} {ℓ₂' : glInverseFunctionals ψ n σ₂}

/-- The block `j = 0` compares two existing unequal-rank gamma equations on
nested actual coefficient models. -/
theorem UnequalRankGammaEquation.eq_of_model_le (hq : 1 < q) (hℓ' : ℓ'.val ≠ 0)
    (hM : coefficientModel π ℓ ≤ coefficientModel π₂ ℓ₂)
    (hM' : coefficientModel σ ℓ' ≤ coefficientModel σ₂ ℓ₂')
    {G G₂ : RationalFunctions}
    (h : UnequalRankGammaEquation hnr q ψ abv μ ν π σ ℓ ℓ' G)
    (h₂ : UnequalRankGammaEquation hnr q ψ abv μ ν π₂ σ₂ ℓ₂ ℓ₂' G₂) : G = G₂ := by
  obtain ⟨ζ, hζ, hall⟩ := h
  obtain ⟨ζ₂, hζ₂, hall₂⟩ := h₂
  have hζ₂small : HasModelMinusOneScalar σ ℓ' ζ₂ :=
    fun f' g => hζ₂ (coefficientModelInclusionMap hM' f') g
  obtain rfl := HasModelMinusOneScalar.unique hℓ' hζ hζ₂small
  have hr : r = n + (0 + (r - n - 1) + 1) := by omega
  obtain ⟨⟨R, hRmem, hR0⟩, hFE⟩ := hall 0 (r - n - 1) hr
  obtain ⟨-, hFE₂⟩ := hall₂ 0 (r - n - 1) hr
  rw [unequalRankValuesAt_eq] at hRmem
  obtain ⟨f, f', hR⟩ := hRmem
  obtain ⟨R₁, Rd₁, hR₁, hRd₁, hN₁⟩ := hFE f f'
  obtain ⟨R₂, Rd₂, hR₂, hRd₂, hN₂⟩ :=
    hFE₂ (coefficientModelInclusionMap hM f) (coefficientModelInclusionMap hM' f')
  obtain rfl := hR.unique hq hR₁
  obtain rfl := hR.unique hq hR₂
  obtain rfl := hRd₁.unique hq hRd₂
  exact hN₁.gamma_unique hq hR0 hN₂

end UnequalRank

section Certificates

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [MeasurableSpace F] {n r : ℕ}
  [MeasurableSpace (Langlands.GeneralLinear (n + 1) F)]
  [BorelSpace (Langlands.GeneralLinear (n + 1) F)]
  [MeasurableSpace (upperUnipotent (n + 1) F)] [BorelSpace (upperUnipotent (n + 1) F)]
  [MeasurableSpace (LeftUnipotentQuotient n F)]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {V₂ : Type uV₂} [AddCommGroup V₂] [Module ℂ V₂]
  {W₂ : Type uW₂} [AddCommGroup W₂] [Module ℂ W₂]
  {q : ℕ} {ψ : UnitaryAdditiveCharacter F} {abv : AbsoluteValue F ℝ}
  {ν : AdditiveHaarMeasure F} {G G₂ : RationalFunctions}

/-- Full equal-rank gamma certificates agree if one pair of their nonzero
functional coefficient models is nested. -/
theorem IsEqualRankGammaFactor.eq_of_model_le
    {π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V}
    {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W}
    {π₂ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V₂}
    {σ₂ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W₂}
    {ℓ : glFunctionals ψ n π} {ℓ' : glInverseFunctionals ψ n σ}
    {ℓ₂ : glFunctionals ψ n π₂} {ℓ₂' : glInverseFunctionals ψ n σ₂}
    (hq : 1 < q) (hℓ : ℓ.val ≠ 0) (hℓ' : ℓ'.val ≠ 0)
    (hℓ₂ : ℓ₂.val ≠ 0) (hℓ₂' : ℓ₂'.val ≠ 0)
    (hM : coefficientModel π ℓ ≤ coefficientModel π₂ ℓ₂)
    (hM' : coefficientModel σ ℓ' ≤ coefficientModel σ₂ ℓ₂')
    (h : IsEqualRankGammaFactor q ψ abv ν π σ G)
    (h₂ : IsEqualRankGammaFactor q ψ abv ν π₂ σ₂ G₂) : G = G₂ := by
  obtain ⟨⟨hinv, μ, hμ⟩, -, -, hall⟩ := h
  exact (@hall hinv μ hμ ℓ ℓ' hℓ hℓ').eq_of_model_le hq hℓ' hM hM'
    (@h₂.2.2.2 hinv μ hμ ℓ₂ ℓ₂' hℓ₂ hℓ₂')

/-- Full unequal-rank gamma certificates agree under the same coefficient-model
inclusions, without a full Whittaker-type hypothesis on any original carrier. -/
theorem IsUnequalRankGammaFactor.eq_of_model_le {hnr : n < r}
    {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V}
    {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W}
    {π₂ : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V₂}
    {σ₂ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W₂}
    {ℓ : glFunctionals ψ r π} {ℓ' : glInverseFunctionals ψ n σ}
    {ℓ₂ : glFunctionals ψ r π₂} {ℓ₂' : glInverseFunctionals ψ n σ₂}
    (hq : 1 < q) (hℓ : ℓ.val ≠ 0) (hℓ' : ℓ'.val ≠ 0)
    (hℓ₂ : ℓ₂.val ≠ 0) (hℓ₂' : ℓ₂'.val ≠ 0)
    (hM : coefficientModel π ℓ ≤ coefficientModel π₂ ℓ₂)
    (hM' : coefficientModel σ ℓ' ≤ coefficientModel σ₂ ℓ₂')
    (h : IsUnequalRankGammaFactor hnr q ψ abv ν π σ G)
    (h₂ : IsUnequalRankGammaFactor hnr q ψ abv ν π₂ σ₂ G₂) : G = G₂ := by
  obtain ⟨⟨hinv, μ, hμ⟩, -, -, hall⟩ := h
  exact (@hall hinv μ hμ ℓ ℓ' hℓ hℓ').eq_of_model_le hq hℓ' hM hM'
    (@h₂.2.2.2 hinv μ hμ ℓ₂ ℓ₂' hℓ₂ hℓ₂')

/-- Compare two existing pair gamma certificates using actual coefficient-model
inclusion for specified nonzero functionals. -/
theorem IsPairGammaFactor.eq_of_model_le
    {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V}
    {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W}
    {π₂ : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V₂}
    {σ₂ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W₂}
    {ℓ : glFunctionals ψ r π} {ℓ' : glInverseFunctionals ψ n σ}
    {ℓ₂ : glFunctionals ψ r π₂} {ℓ₂' : glInverseFunctionals ψ n σ₂}
    (hq : 1 < q) (hℓ : ℓ.val ≠ 0) (hℓ' : ℓ'.val ≠ 0)
    (hℓ₂ : ℓ₂.val ≠ 0) (hℓ₂' : ℓ₂'.val ≠ 0)
    (hM : coefficientModel π ℓ ≤ coefficientModel π₂ ℓ₂)
    (hM' : coefficientModel σ ℓ' ≤ coefficientModel σ₂ ℓ₂')
    (h : IsPairGammaFactor q ψ abv ν π σ G)
    (h₂ : IsPairGammaFactor q ψ abv ν π₂ σ₂ G₂) : G = G₂ := by
  by_cases hnr : n < r
  · rw [isPairGammaFactor_of_lt hnr] at h h₂
    exact h.eq_of_model_le hq hℓ hℓ' hℓ₂ hℓ₂' hM hM' h₂
  · by_cases hrn : r = n
    · subst r
      rw [isPairGammaFactor_self] at h h₂
      exact h.eq_of_model_le hq hℓ hℓ' hℓ₂ hℓ₂' hM hM' h₂
    · exact absurd h (not_isPairGammaFactor_of_lt (by omega))

end Certificates

end Langlands.RankinSelberg
