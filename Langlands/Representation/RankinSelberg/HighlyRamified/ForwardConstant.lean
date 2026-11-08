import Langlands.Representation.RankinSelberg.HighlyRamified.AdjacentComparison
import Langlands.Representation.RankinSelberg.HighlyRamified.ConstantForward

/-!
# A monomial gamma factor and a monomial dual integral give a constant corank-one integral

For an adjacent-rank pair `(Π, τ)` with gamma factor `C X^N` and model vectors `f`, `W''`
whose dual corank-one integral is `c_d X^(-N)` on a right half-plane, the corank-one integral
`Ψ(s, f, W'')` is the constant `(ζ^(m+1))⁻¹ C⁻¹ c_d q^N` on a right half-plane, where `ζ` is
the minus-one scalar of the model of `τ`. The constant `c_d` may vanish.
-/

noncomputable section

namespace Langlands.RankinSelberg.HighlyRamified

open MeasureTheory HarmonicAnalysis Whittaker QuotientIntegration GeneralLinear

universe uF uV uX

/-- `forward_eq_const_of_monomial` for an arbitrary, possibly zero, dual constant. -/
theorem forward_eq_const_of_monomial' {q : ℕ} (hq : 1 < q) {ζ : ℂˣ} {e : ℕ}
    {R Rd : RationalFunctions} {I J : ℂ → ℂ} (C : ℂˣ) (N : ℤ) (cd : ℂ)
    (hR : HasRationalContinuation q I R) (hRd : HasRationalContinuation q J Rd)
    (hFE : GammaFunctionalEquation q ζ e (rationalEpsilonMonomial C N : RationalFunctions) R Rd)
    (hJ : ∃ b : ℝ, ∀ s : ℂ, b < s.re → J s = cd * (spectralPoint q s) ^ (-N)) :
    ∃ a : ℝ, ∀ s : ℂ, a < s.re →
      I s = (((ζ : ℂ) ^ e))⁻¹ * (C : ℂ)⁻¹ * cd * (q : ℂ) ^ N := by
  by_cases hcd : cd = 0
  · subst hcd
    have hq0 : 0 < q := by omega
    have hsp : ∀ s, spectralPoint q s ≠ 0 := spectralPoint_ne_zero_of_pos hq0
    obtain ⟨b, hb⟩ := hJ
    have h0 : HasRationalContinuation q J 0 :=
      ⟨b, fun s hs => ⟨by simp, by rw [hb s hs]; simp⟩⟩
    have hRd0 : Rd = 0 := hRd.unique hq h0
    obtain ⟨a, ha⟩ := hR
    refine ⟨a, fun s hs => ?_⟩
    obtain ⟨hden, hI⟩ := ha s hs
    have h := hFE s hden (by rw [hRd0]; simp) (regular_rationalEpsilonMonomial C N (hsp s))
    rw [hRd0, eval_rationalEpsilonMonomial C N (hsp s)] at h
    have hζ : ((ζ : ℂ) ^ e) ≠ 0 := pow_ne_zero _ ζ.ne_zero
    have hX : (spectralPoint q s) ^ N ≠ 0 := zpow_ne_zero _ (hsp s)
    have hR0 : RatFunc.eval (RingHom.id ℂ) (spectralPoint q s) R = 0 := by
      have h' : (ζ : ℂ) ^ e * ((C : ℂ) * spectralPoint q s ^ N *
          RatFunc.eval (RingHom.id ℂ) (spectralPoint q s) R) = 0 := by
        rw [← h]; simp
      rcases mul_eq_zero.mp h' with h1 | h1
      · exact absurd h1 hζ
      · rcases mul_eq_zero.mp h1 with h2 | h2
        · exact absurd h2 (mul_ne_zero C.ne_zero hX)
        · exact h2
    rw [hI, hR0]
    simp
  · exact forward_eq_const_of_monomial hq C N (Units.mk0 cd hcd) hR hRd hFE hJ

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance forwardConstantFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance forwardConstantValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance forwardConstantLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance forwardConstantFieldMeasurable : MeasurableSpace F.Carrier := borel _
local instance forwardConstantFieldBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance forwardConstantGroupMeasurable (r : ℕ) :
    MeasurableSpace (GeneralLinear (r + 1) F.Carrier) := borel _
local instance forwardConstantGroupBorel (r : ℕ) :
    BorelSpace (GeneralLinear (r + 1) F.Carrier) := ⟨rfl⟩
local instance forwardConstantUnipotentMeasurable (r : ℕ) : MeasurableSpace
    (upperUnipotent (r + 1) F.Carrier) := borel _
local instance forwardConstantUnipotentBorel (r : ℕ) : BorelSpace
    (upperUnipotent (r + 1) F.Carrier) := ⟨rfl⟩
local instance forwardConstantQuotientMeasurable (r : ℕ) : MeasurableSpace
    (LeftUnipotentQuotient r F.Carrier) := borel _
local instance forwardConstantQuotientBorel (r : ℕ) : BorelSpace
    (LeftUnipotentQuotient r F.Carrier) := ⟨rfl⟩

local notation "abv" => normalizedAbsoluteValue F.canonicalTopologicalData
local notation "qF" => F.canonicalTopologicalData.residueCardinality

/-- A monomial gamma factor and a monomial dual corank-one integral make the corank-one
integral constant on a right half-plane. -/
theorem corankOne_eq_const_of_gamma_monomial
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier) {m : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V] {X : Type uX} [AddCommGroup X] [Module ℂ X]
    {Pi : Representation ℂ (GeneralLinear (m + 1 + 1) F.Carrier) V}
    {τ : Representation ℂ (GeneralLinear (m + 1) F.Carrier) X} {G : RationalFunctions}
    (hG : IsPadicPairGammaFactor F ψ ν Pi τ G)
    (ℓ : glFunctionals ψ (m + 1) Pi) (hℓ : ℓ.val ≠ 0)
    (ℓ'' : glInverseFunctionals ψ m τ) (hℓ'' : ℓ''.val ≠ 0)
    (f : (coefficientModel Pi ℓ).toSubmodule) (W'' : (coefficientModel τ ℓ'').toSubmodule)
    (C : ℂˣ) (N : ℤ) (hGC : G = rationalEpsilonMonomial C N) (cd : ℂ)
    (hJ : ∃ b : ℝ, ∀ s : ℂ, b < s.re →
      corankOneIntegral (ψ.scale (-1)) abv (unipotentQuotientHaar F.Carrier m)
          (firstDualFunction ψ (m + 1) f.val) (secondDualFunction ψ m W''.val) s =
        cd * (spectralPoint qF s) ^ (-N)) :
    ∃ ζ : ℂˣ, HasModelMinusOneScalar τ ℓ'' ζ ∧ ∃ a : ℝ, ∀ s : ℂ, a < s.re →
      corankOneIntegral ψ abv (unipotentQuotientHaar F.Carrier m) f.val W''.val s =
        (((ζ : ℂ) ^ (m + 1)))⁻¹ * (C : ℂ)⁻¹ * cd * (qF : ℂ) ^ N := by
  have hq : 1 < qF := PadicField.TopologicalData.residueCardinality_gt_one _
  have hnr : m < m + 1 := Nat.lt_succ_self m
  have hμ := unipotentQuotientHaar_isCompatible F.Carrier m
  have e : IsPairGammaFactor qF ψ abv ν Pi τ G := hG
  rw [isPairGammaFactor_of_lt hnr] at e
  obtain ⟨-, -, -, hall⟩ := e
  obtain ⟨ζ, hζ, hFE⟩ := hall (unipotentQuotientHaar F.Carrier m) hμ ℓ ℓ'' hℓ hℓ''
  obtain ⟨-, hT⟩ := hFE 0 0 rfl
  obtain ⟨R, Rd, hR, hRd, hN⟩ := hT f W''
  have hR' : HasRationalContinuation qF
      (corankOneIntegral ψ abv (unipotentQuotientHaar F.Carrier m) f.val W''.val) R := by
    have hfun : corankOneIntegral ψ abv (unipotentQuotientHaar F.Carrier m) f.val W''.val =
        unequalRankIntegralAt 0 0 rfl ψ abv (unipotentQuotientHaar F.Carrier m)
          (rectangularMeasure ν 0 (m + 1)) f.val W''.val :=
      funext fun s => Padic.corankOneIntegral_eq_zeroZero F ψ _ ν _ _ s
    rw [hfun]
    exact hR
  have hRd' : HasRationalContinuation qF
      (corankOneIntegral (ψ.scale (-1)) abv (unipotentQuotientHaar F.Carrier m)
        (firstDualFunction ψ (m + 1) f.val) (secondDualFunction ψ m W''.val)) Rd := by
    have hfun : dualUnequalRankModelIntegralAt hnr 0 0 rfl ψ abv
        (unipotentQuotientHaar F.Carrier m) ν Pi τ ℓ ℓ'' f W'' =
        corankOneIntegral (ψ.scale (-1)) abv (unipotentQuotientHaar F.Carrier m)
          (firstDualFunction ψ (m + 1) f.val) (secondDualFunction ψ m W''.val) :=
      funext fun s => Padic.adjacentRank_dualUnequalRankIntegral_eq_corank F ψ _ ν Pi τ ℓ ℓ'' f W'' s
    rw [← hfun]
    exact hRd
  rw [hGC] at hN
  exact ⟨ζ, hζ, forward_eq_const_of_monomial' hq C N cd hR' hRd' hN hJ⟩

end Langlands.RankinSelberg.HighlyRamified
