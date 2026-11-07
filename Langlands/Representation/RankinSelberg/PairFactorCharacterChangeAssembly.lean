import Langlands.Representation.RankinSelberg.PairFactorCharacterChangeStatement
import Langlands.Representation.RankinSelberg.PairFactorCharacterChangeMeasures
import Langlands.Representation.RankinSelberg.AdjacentRankLargeTwistLDivisibility

/-!
# Assembly of the unequal-rank character-change statement

The L-polynomial half is the Library theorem
`Padic.isPadicSymmetricLPolynomial_characterChange`. The epsilon half is reduced
to the fixed-functional transport `FixedFunctionalEpsilonTransport`: for one
compatible quotient measure and one pair of functionals for `ψ`, the
fixed-monomial functional equation for `ψ` gives the one for `ψ^a` with the
translated functionals and the changed monomial.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance pfccTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance pfccValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance pfccLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance pfccMeasurable : MeasurableSpace F.Carrier := borel _
local instance pfccBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance pfccGroupMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := borel _
local instance pfccGroupBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
local instance pfccUnipotentMeasurable (n : ℕ) :
    MeasurableSpace (upperUnipotent (n + 1) F.Carrier) := borel _
local instance pfccUnipotentBorel (n : ℕ) :
    BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
local instance pfccQuotientMeasurable (n : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient n F.Carrier) := borel _

local notation "abv" => normalizedAbsoluteValue F.canonicalTopologicalData
local notation "qF" => F.canonicalTopologicalData.residueCardinality

/-- Theorem: the L-polynomial half. -/
theorem unequalRankLPolynomialCharacterChange :
    UnequalRankLPolynomialCharacterChangeStatement.{uF, uV, uW} := by
  intro p _ F r t V _ _ W _ _ π σ _ _ _ _ _ ψ ν a P h
  exact (Padic.isPadicSymmetricLPolynomial_characterChange F ψ a ν π σ P).mp h

/-- The fixed-functional transport of the unequal-rank epsilon equation from
`ψ` and `ν` to `ψ^a` and `ν'`, with the coefficient changed by
`ω_π(a)^(n+1) ω_σ(a)^(r+1) |a|^(-N/2)` and the exponent by `N ord a`,
`N = (r+1)(n+1)`. -/
def FixedFunctionalEpsilonTransport {r n : ℕ} (hnr : n < r)
    {V : Type uV} [AddCommGroup V] [Module ℂ V] {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
    (ωπ ωσ : F.Carrierˣ →* ℂˣ) (ψ : UnitaryAdditiveCharacter F.Carrier)
    (ν ν' : AdditiveHaarMeasure F.Carrier) (a : F.Carrierˣ) : Prop :=
  ∀ [Measure.IsMulRightInvariant (unipotentHaar F.Carrier n)]
    (μ : Measure (LeftUnipotentQuotient n F.Carrier)),
    IsCompatible (upperUnipotent (n + 1) F.Carrier) (generalLinearHaar F.Carrier n)
      (unipotentHaar F.Carrier n) μ →
    ∀ (ℓ : glFunctionals ψ r π) (ℓ' : glInverseFunctionals ψ n σ) (c : ℂˣ) (m : ℤ),
      UnequalRankEpsilonEquation hnr qF ψ abv μ ν π σ ℓ ℓ' c m →
      ∃ c' : ℂˣ,
        (c' : ℂ) = (c : ℂ) * ((ωπ a : ℂˣ) : ℂ) ^ (n + 1) * ((ωσ a : ℂˣ) : ℂ) ^ (r + 1) *
          ((F.canonicalTopologicalData.normalizedAbs (a : F.Carrier) : ℝ) : ℂ) ^
            (-(((r + 1) * (n + 1) : ℕ) : ℂ) / 2) ∧
        UnequalRankEpsilonEquation hnr qF (ψ.scale a) abv μ ν' π σ
          (characterChangeFunctional ψ π a ℓ) (characterChangeInverseFunctional ψ σ a ℓ') c'
          (m + ((r + 1) * (n + 1) : ℕ) * F.canonicalTopologicalData.ord (a : F.Carrier))

omit [Fact p.Prime] in
/-- A linear equivalence of submodules preserves nonvanishing of the underlying element. -/
theorem val_ne_zero_of_linearEquiv {M₁ M₂ : Type*} [AddCommGroup M₁] [Module ℂ M₁]
    [AddCommGroup M₂] [Module ℂ M₂] {S₁ : Submodule ℂ M₁} {S₂ : Submodule ℂ M₂}
    (φ : S₁ ≃ₗ[ℂ] S₂) {x : S₁} (hx : x.val ≠ 0) : (φ x).val ≠ 0 := by
  intro h
  apply hx
  have h0 : φ x = 0 := Subtype.ext h
  rw [φ.map_eq_zero_iff] at h0
  rw [h0]
  rfl

/-- `|a|^(-N/2)` is nonzero. -/
theorem normalizedAbs_cpow_ne_zero (a : F.Carrierˣ) (z : ℂ) :
    ((F.canonicalTopologicalData.normalizedAbs (a : F.Carrier) : ℝ) : ℂ) ^ z ≠ 0 := by
  have hpos : 0 < F.canonicalTopologicalData.normalizedAbs (a : F.Carrier) := by
    rw [← LocalFactor.PadicAbelian.sqrtNormalizedAbs_sq F a]
    have := LocalFactor.PadicAbelian.sqrtNormalizedAbs_pos F a
    positivity
  rw [Ne, Complex.cpow_eq_zero_iff]
  intro h
  exact hpos.ne' (by exact_mod_cast h.1)

/-- The unequal-rank epsilon relation transports along a fixed-functional
transport, with the explicit change of the monomial. -/
theorem isUnequalRankEpsilonFactor_characterChange_of_transport {r n : ℕ} (hnr : n < r)
    {V : Type uV} [AddCommGroup V] [Module ℂ V] {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
    (ωπ ωσ : F.Carrierˣ →* ℂˣ) (ψ : UnitaryAdditiveCharacter F.Carrier)
    (ν ν' : AdditiveHaarMeasure F.Carrier) (a : F.Carrierˣ)
    (htrans : FixedFunctionalEpsilonTransport F hnr π σ ωπ ωσ ψ ν ν' a)
    (e : ℂˣ × ℤ) (h : IsUnequalRankEpsilonFactor hnr qF ψ abv ν π σ e) :
    ∃ e' : ℂˣ × ℤ,
      IsUnequalRankEpsilonFactor hnr qF (ψ.scale a) abv ν' π σ e' ∧
      e'.2 = e.2 + ((r + 1) * (n + 1) : ℕ) * F.canonicalTopologicalData.ord (a : F.Carrier) ∧
      (e'.1 : ℂ) = (e.1 : ℂ) * ((ωπ a : ℂˣ) : ℂ) ^ (n + 1) * ((ωσ a : ℂˣ) : ℂ) ^ (r + 1) *
        ((F.canonicalTopologicalData.normalizedAbs (a : F.Carrier) : ℝ) : ℂ) ^
          (-(((r + 1) * (n + 1) : ℕ) : ℂ) / 2) := by
  set N : ℕ := (r + 1) * (n + 1)
  let c' : ℂˣ := e.1 * ωπ a ^ (n + 1) * ωσ a ^ (r + 1) *
    Units.mk0 _ (normalizedAbs_cpow_ne_zero F a (-((N : ℕ) : ℂ) / 2))
  have hc' : (c' : ℂ) = (e.1 : ℂ) * ((ωπ a : ℂˣ) : ℂ) ^ (n + 1) *
      ((ωσ a : ℂˣ) : ℂ) ^ (r + 1) *
        ((F.canonicalTopologicalData.normalizedAbs (a : F.Carrier) : ℝ) : ℂ) ^
          (-((N : ℕ) : ℂ) / 2) := by
    simp only [c', Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mk0]
  obtain ⟨hmeas, ⟨ℓ₀, hℓ₀⟩, ⟨ℓ₀', hℓ₀'⟩, hall⟩ := h
  refine ⟨(c', e.2 + (N : ℤ) * F.canonicalTopologicalData.ord (a : F.Carrier)),
    ⟨hmeas, ⟨characterChangeFunctional ψ π a ℓ₀,
      val_ne_zero_of_linearEquiv (characterChangeFunctionalEquiv ψ π a) hℓ₀⟩,
      ⟨characterChangeInverseFunctional ψ σ a ℓ₀',
        val_ne_zero_of_linearEquiv (characterChangeInverseFunctionalEquiv ψ σ a) hℓ₀'⟩, ?_⟩,
    rfl, hc'⟩
  intro _ μ hμ ℓ ℓ' hℓ hℓ'
  let ℓO := (characterChangeFunctionalEquiv ψ π a).symm ℓ
  let ℓO' := (characterChangeInverseFunctionalEquiv ψ σ a).symm ℓ'
  have hℓO : ℓO.val ≠ 0 :=
    val_ne_zero_of_linearEquiv (characterChangeFunctionalEquiv ψ π a).symm hℓ
  have hℓO' : ℓO'.val ≠ 0 :=
    val_ne_zero_of_linearEquiv (characterChangeInverseFunctionalEquiv ψ σ a).symm hℓ'
  obtain ⟨c'', hc'', hE⟩ := htrans μ hμ ℓO ℓO' e.1 e.2 (hall μ hμ ℓO ℓO' hℓO hℓO')
  have hL : characterChangeFunctional ψ π a ℓO = ℓ :=
    (characterChangeFunctionalEquiv ψ π a).apply_symm_apply ℓ
  have hL' : characterChangeInverseFunctional ψ σ a ℓO' = ℓ' :=
    (characterChangeInverseFunctionalEquiv ψ σ a).apply_symm_apply ℓ'
  have hcc : c'' = c' := Units.ext (hc''.trans hc'.symm)
  rw [hL, hL', hcc] at hE
  exact hE

/-- The fixed-functional transport for every pair of unequal rank with central
characters `ω_π`, `ω_σ`, and every pair of Haar measures with `ν' = κ ν`,
`κ² = |a|`. -/
def FixedFunctionalEpsilonTransportStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) {r n : ℕ} (hnr : n < r)
    {V : Type uV} [AddCommGroup V] [Module ℂ V] {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
    (ωπ ωσ : F.Carrierˣ →* ℂˣ),
    Classification.HasGLCentralCharacter F.Carrier (r + 1) π ωπ →
    Classification.HasGLCentralCharacter F.Carrier (n + 1) σ ωσ →
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier) (ν ν' : AdditiveHaarMeasure F.Carrier)
      (a : F.Carrierˣ) (κ : NNReal),
      ν'.measure = κ • ν.measure →
      (κ : ℝ) ^ 2 = F.canonicalTopologicalData.normalizedAbs (a : F.Carrier) →
      FixedFunctionalEpsilonTransport F hnr π σ ωπ ωσ ψ ν ν' a

/-- Theorem: the epsilon half for both rank orders, from the fixed-functional
transport in both carrier-universe orders. The pair is read with the larger rank
first, and the self-dual measures differ by `|a|^(1/2)`. -/
theorem unequalRankEpsilonCharacterChange_of_transport
    (h₁ : FixedFunctionalEpsilonTransportStatement.{uF, uV, uW})
    (h₂ : FixedFunctionalEpsilonTransportStatement.{uF, uW, uV}) :
    UnequalRankEpsilonCharacterChangeStatement.{uF, uV, uW} := by
  intro p _ F r t V _ _ W _ _ π σ ωπ ωσ hrt _ _ _ _ hωπ hωσ ψ ν a ν' e he
  have hκ : ν'.val.measure =
      LocalFactor.PadicAbelian.sqrtNormalizedAbs F a • ν.val.measure := by
    rw [LocalFactor.PadicAbelian.SelfDualHaar.val_eq_scale F ψ a ν ν',
      AdditiveHaarMeasure.scale_measure]
  have hκ2 := LocalFactor.PadicAbelian.sqrtNormalizedAbs_sq F a
  rcases Nat.lt_or_gt_of_ne hrt with hlt | hlt
  · obtain ⟨e', h1, h2, h3⟩ := isUnequalRankEpsilonFactor_characterChange_of_transport F hlt
      σ π ωσ ωπ ψ ν.val ν'.val a
      (h₂ p F hlt σ π ωσ ωπ hωσ hωπ ψ ν.val ν'.val a _ hκ hκ2) e
      ((isPairEpsilonFactor_of_lt hlt).mp ((isPadicSymmetricEpsilonFactor_of_lt hlt).mp he))
    refine ⟨e', (isPadicSymmetricEpsilonFactor_of_lt hlt).mpr
      ((isPairEpsilonFactor_of_lt hlt).mpr h1), ?_, ?_⟩
    · rw [h2, Nat.mul_comm]
    · rw [h3, Nat.mul_comm (t + 1)]
      ring
  · obtain ⟨e', h1, h2, h3⟩ := isUnequalRankEpsilonFactor_characterChange_of_transport F hlt
      π σ ωπ ωσ ψ ν.val ν'.val a
      (h₁ p F hlt π σ ωπ ωσ hωπ hωσ ψ ν.val ν'.val a _ hκ hκ2) e
      ((isPairEpsilonFactor_of_lt hlt).mp
        ((isPadicSymmetricEpsilonFactor_of_le hlt.le).mp he))
    exact ⟨e', (isPadicSymmetricEpsilonFactor_of_le hlt.le).mpr
      ((isPairEpsilonFactor_of_lt hlt).mpr h1), h2, h3⟩

/-- Theorem: the change of additive character for unequal-rank pair factors,
from the fixed-functional transport in both carrier-universe orders. -/
theorem pairFactorCharacterChange_of_transport
    (h₁ : FixedFunctionalEpsilonTransportStatement.{uF, uV, uW})
    (h₂ : FixedFunctionalEpsilonTransportStatement.{uF, uW, uV}) :
    PairFactorCharacterChangeStatement.{uF, uV, uW} :=
  ⟨unequalRankLPolynomialCharacterChange, unequalRankEpsilonCharacterChange_of_transport h₁ h₂⟩

end Langlands.RankinSelberg
