import Langlands.Representation.RankinSelberg.AdjacentRankGammaComparison
import Langlands.Representation.RankinSelberg.AdjacentRankImageLDivisibility
import Langlands.Representation.RankinSelberg.UnipotentQuotient

/-!
# Comparing adjacent-rank gamma factors through test vectors

Two candidates of rank `n + 2` against one test of rank `n + 1` have the same gamma
factor as soon as some coefficient-model vectors have equal corank-one integrals on a
right half-plane and the same nonzero constant dual integral there.
-/

noncomputable section

namespace Langlands.RankinSelberg.HighlyRamified

open MeasureTheory HarmonicAnalysis Whittaker QuotientIntegration GeneralLinear

universe uF uV₁ uV₂ uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance adjacentComparisonFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance adjacentComparisonValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance adjacentComparisonLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance adjacentComparisonFieldMeasurable : MeasurableSpace F.Carrier := borel _
local instance adjacentComparisonFieldBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance adjacentComparisonGroupMeasurable (r : ℕ) :
    MeasurableSpace (GeneralLinear (r + 1) F.Carrier) := borel _
local instance adjacentComparisonGroupBorel (r : ℕ) :
    BorelSpace (GeneralLinear (r + 1) F.Carrier) := ⟨rfl⟩
local instance adjacentComparisonUnipotentMeasurable (r : ℕ) : MeasurableSpace
    (upperUnipotent (r + 1) F.Carrier) := borel _
local instance adjacentComparisonUnipotentBorel (r : ℕ) : BorelSpace
    (upperUnipotent (r + 1) F.Carrier) := ⟨rfl⟩
local instance adjacentComparisonQuotientMeasurable (r : ℕ) : MeasurableSpace
    (LeftUnipotentQuotient r F.Carrier) := borel _
local instance adjacentComparisonQuotientBorel (r : ℕ) : BorelSpace
    (LeftUnipotentQuotient r F.Carrier) := ⟨rfl⟩

local notation "abv" => normalizedAbsoluteValue F.canonicalTopologicalData
local notation "qF" => F.canonicalTopologicalData.residueCardinality

/-- A function equal to a constant on a right half-plane has that constant as its
rational continuation. -/
theorem hasRationalContinuation_const_of_eventually (q : ℕ) {f : ℂ → ℂ}
    {c : ℂ} {a : ℝ} (hf : ∀ s : ℂ, a < s.re → f s = c) :
    HasRationalContinuation q f (algebraMap ℂ RationalFunctions c) := by
  refine ⟨a, fun s hs => ⟨?_, ?_⟩⟩
  · rw [RatFunc.algebraMap_eq_C, RatFunc.denom_C]
    simp
  · rw [hf s hs, RatFunc.algebraMap_eq_C, RatFunc.eval_C]
    rfl

/-- Two adjacent-rank gamma factors agree when one triple of test vectors has equal
corank-one integrals on a right half-plane and the same nonzero constant dual integral. -/
theorem gamma_eq_of_adjacent_tests
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier) {n : ℕ}
    {V₁ : Type uV₁} [AddCommGroup V₁] [Module ℂ V₁]
    {V₂ : Type uV₂} [AddCommGroup V₂] [Module ℂ V₂]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    {π₁ : Representation ℂ (GeneralLinear (n + 1 + 1) F.Carrier) V₁}
    {π₂ : Representation ℂ (GeneralLinear (n + 1 + 1) F.Carrier) V₂}
    {σ : Representation ℂ (GeneralLinear (n + 1) F.Carrier) W}
    {G₁ G₂ : RationalFunctions}
    (h₁ : IsPadicPairGammaFactor F ψ ν π₁ σ G₁) (h₂ : IsPadicPairGammaFactor F ψ ν π₂ σ G₂)
    (ℓ₁ : glFunctionals ψ (n + 1) π₁) (hℓ₁ : ℓ₁.val ≠ 0)
    (ℓ₂ : glFunctionals ψ (n + 1) π₂) (hℓ₂ : ℓ₂.val ≠ 0)
    (ℓ' : glInverseFunctionals ψ n σ) (hℓ' : ℓ'.val ≠ 0)
    (f₁ : (coefficientModel π₁ ℓ₁).toSubmodule) (f₂ : (coefficientModel π₂ ℓ₂).toSubmodule)
    (f' : (coefficientModel σ ℓ').toSubmodule)
    (hI : ∃ a : ℝ, ∀ s : ℂ, a < s.re →
      corankOneIntegral ψ abv (unipotentQuotientHaar F.Carrier n) f₁.val f'.val s =
        corankOneIntegral ψ abv (unipotentQuotientHaar F.Carrier n) f₂.val f'.val s)
    (hJ : ∃ (a : ℝ) (c : ℂ), c ≠ 0 ∧ ∀ s : ℂ, a < s.re →
      corankOneIntegral (ψ.scale (-1)) abv (unipotentQuotientHaar F.Carrier n)
          (firstDualFunction ψ (n + 1) f₁.val) (secondDualFunction ψ n f'.val) s = c ∧
      corankOneIntegral (ψ.scale (-1)) abv (unipotentQuotientHaar F.Carrier n)
          (firstDualFunction ψ (n + 1) f₂.val) (secondDualFunction ψ n f'.val) s = c) :
    G₁ = G₂ := by
  have hq : 1 < qF := PadicField.TopologicalData.residueCardinality_gt_one _
  have hnr : n < n + 1 := Nat.lt_succ_self n
  have hμ := unipotentQuotientHaar_isCompatible F.Carrier n
  have e₁ : IsPairGammaFactor qF ψ abv ν π₁ σ G₁ := h₁
  have e₂ : IsPairGammaFactor qF ψ abv ν π₂ σ G₂ := h₂
  rw [isPairGammaFactor_of_lt hnr] at e₁ e₂
  obtain ⟨-, -, -, hall₁⟩ := e₁
  obtain ⟨-, -, -, hall₂⟩ := e₂
  obtain ⟨ζ₁, hζ₁, hFE₁⟩ := hall₁ (unipotentQuotientHaar F.Carrier n) hμ ℓ₁ ℓ' hℓ₁ hℓ'
  obtain ⟨ζ₂, hζ₂, hFE₂⟩ := hall₂ (unipotentQuotientHaar F.Carrier n) hμ ℓ₂ ℓ' hℓ₂ hℓ'
  obtain rfl := HasModelMinusOneScalar.unique hℓ' hζ₁ hζ₂
  obtain ⟨-, hT₁⟩ := hFE₁ 0 0 rfl
  obtain ⟨-, hT₂⟩ := hFE₂ 0 0 rfl
  obtain ⟨R₁, Rd₁, hR₁, hRd₁, hN₁⟩ := hT₁ f₁ f'
  obtain ⟨R₂, Rd₂, hR₂, hRd₂, hN₂⟩ := hT₂ f₂ f'
  obtain ⟨aI, hIa⟩ := hI
  obtain ⟨aJ, c, hc, hJa⟩ := hJ
  -- The forward continuations agree.
  have hR₁' : HasRationalContinuation qF
      (corankOneIntegral ψ abv (unipotentQuotientHaar F.Carrier n) f₁.val f'.val) R₁ := by
    have hfun : corankOneIntegral ψ abv (unipotentQuotientHaar F.Carrier n) f₁.val f'.val =
        unequalRankIntegralAt 0 0 rfl ψ abv (unipotentQuotientHaar F.Carrier n)
          (rectangularMeasure ν 0 (n + 1)) f₁.val f'.val :=
      funext fun s => Padic.corankOneIntegral_eq_zeroZero F ψ _ ν _ _ s
    rw [hfun]
    exact hR₁
  have hR₂' : HasRationalContinuation qF
      (corankOneIntegral ψ abv (unipotentQuotientHaar F.Carrier n) f₂.val f'.val) R₂ := by
    have hfun : corankOneIntegral ψ abv (unipotentQuotientHaar F.Carrier n) f₂.val f'.val =
        unequalRankIntegralAt 0 0 rfl ψ abv (unipotentQuotientHaar F.Carrier n)
          (rectangularMeasure ν 0 (n + 1)) f₂.val f'.val :=
      funext fun s => Padic.corankOneIntegral_eq_zeroZero F ψ _ ν _ _ s
    rw [hfun]
    exact hR₂
  have hR₂₁ : HasRationalContinuation qF
      (corankOneIntegral ψ abv (unipotentQuotientHaar F.Carrier n) f₁.val f'.val) R₂ := by
    obtain ⟨b, hb⟩ := hR₂'
    refine ⟨max aI b, fun s hs => ⟨(hb s ((le_max_right _ _).trans_lt hs)).1, ?_⟩⟩
    rw [hIa s ((le_max_left _ _).trans_lt hs)]
    exact (hb s ((le_max_right _ _).trans_lt hs)).2
  obtain rfl := hR₁'.unique hq hR₂₁
  -- Both dual continuations are the constant `c`.
  have hRd₁' : HasRationalContinuation qF
      (corankOneIntegral (ψ.scale (-1)) abv (unipotentQuotientHaar F.Carrier n)
        (firstDualFunction ψ (n + 1) f₁.val) (secondDualFunction ψ n f'.val)) Rd₁ := by
    have hfun : dualUnequalRankModelIntegralAt hnr 0 0 rfl ψ abv
        (unipotentQuotientHaar F.Carrier n) ν π₁ σ ℓ₁ ℓ' f₁ f' =
        corankOneIntegral (ψ.scale (-1)) abv (unipotentQuotientHaar F.Carrier n)
          (firstDualFunction ψ (n + 1) f₁.val) (secondDualFunction ψ n f'.val) :=
      funext fun s => Padic.adjacentRank_dualUnequalRankIntegral_eq_corank F ψ _ ν π₁ σ ℓ₁ ℓ' f₁ f' s
    rw [← hfun]
    exact hRd₁
  have hRd₂' : HasRationalContinuation qF
      (corankOneIntegral (ψ.scale (-1)) abv (unipotentQuotientHaar F.Carrier n)
        (firstDualFunction ψ (n + 1) f₂.val) (secondDualFunction ψ n f'.val)) Rd₂ := by
    have hfun : dualUnequalRankModelIntegralAt hnr 0 0 rfl ψ abv
        (unipotentQuotientHaar F.Carrier n) ν π₂ σ ℓ₂ ℓ' f₂ f' =
        corankOneIntegral (ψ.scale (-1)) abv (unipotentQuotientHaar F.Carrier n)
          (firstDualFunction ψ (n + 1) f₂.val) (secondDualFunction ψ n f'.val) :=
      funext fun s => Padic.adjacentRank_dualUnequalRankIntegral_eq_corank F ψ _ ν π₂ σ ℓ₂ ℓ' f₂ f' s
    rw [← hfun]
    exact hRd₂
  have hc₁ := hasRationalContinuation_const_of_eventually qF
    (fun s hs => (hJa s hs).1)
  have hc₂ := hasRationalContinuation_const_of_eventually qF
    (fun s hs => (hJa s hs).2)
  obtain rfl := hRd₁'.unique hq hc₁
  obtain rfl := hRd₂'.unique hq hc₂
  -- The forward continuation is nonzero, since the constant dual value is nonzero.
  have hR0 : R₁ ≠ 0 := by
    intro hz
    obtain ⟨t, ht⟩ := (finite_spectralPoint_roots hq (RatFunc.denom_ne_zero G₁)).infinite_compl.nonempty
    have hden : R₁.denom.eval (spectralPoint qF (t : ℂ)) ≠ 0 := by
      rw [hz, RatFunc.denom_zero]
      simp
    have hdual : (algebraMap ℂ RationalFunctions c).denom.eval
        (spectralPoint qF (1 - (t : ℂ))) ≠ 0 := by
      rw [RatFunc.algebraMap_eq_C, RatFunc.denom_C]
      simp
    have hG : G₁.denom.eval (spectralPoint qF (t : ℂ)) ≠ 0 := ht
    have h := hN₁ t hden hdual hG
    rw [hz, RatFunc.algebraMap_eq_C, RatFunc.eval_C] at h
    simp at h
    exact hc h
  exact hN₁.gamma_unique hq hR0 hN₂

end Langlands.RankinSelberg.HighlyRamified
