import Langlands.Representation.RankinSelberg.UnramifiedFactorStatement
import Langlands.Representation.RankinSelberg.AnalyticStatement

/-!
# Equal-rank integrals of Jacquet and Shalika, Euler products I

Jacquet and Shalika, *On Euler products and the classification of automorphic
representations I*, Proposition (1.5), printed pages 507–510, and Proposition (2.3),
printed pages 511–512. For irreducible unitary generic representations `π` and `σ` of
`GL_(n+1)(F)` the equal-rank integrals `Ψ(s, W, W', Φ)` converge absolutely in
`Re s ≥ 1`, and for every nonzero `W` and every such `s` some `W'` and `Φ` give a
nonzero value. For generic unramified `π` and `σ`, with no unitarity hypothesis, the
integral of the normalized spherical vectors against the characteristic function of
`O^(n+1)` is `det(1 - A ⊗ A' q^(-s))⁻¹` for `Re s` large.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear Langlands.Conductor
open Langlands.Correspondence QuotientIntegration

universe uF uV uW

/-- Jacquet–Shalika, Euler products I, Proposition (2.3), printed pages 511–512: let `π`
and `σ` be unramified generic representations of `GL_(n+1)(F)`, not necessarily unitary,
with Langlands classes `A = diag(χ_i(ϖ))` and `A' = diag(χ'_j(ϖ))`, and take Jacquet's
normalizations (`q` the residue cardinality, the normalized absolute value, `ψ` of
conductor `O`, and the quotient measure on `N_(n+1) \ GL_(n+1)` from the Haar measures
giving `GL_(n+1)(O)` and `N_(n+1)(O)` mass one). For the normalized spherical vectors
`W₀` of a `ψ`-Whittaker model of `π` and `W₀'` of a `ψ⁻¹`-Whittaker model of `σ`, the
integral `Ψ(s, W₀, W₀', Φ°) = ∫ W₀(g) W₀'(g) Φ°(e_(n+1) g) |det g|^s dg` converges for
`Re s` large and equals `det(1 - A ⊗ A' q^(-s))⁻¹`. -/
def UnramifiedGenericEqualRankIntegralStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (n : ℕ)
    {V : Type uV} [AddCommGroup V] [Module ℂ V] {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
    (χ χ' : Fin (n + 1) → QuasiCharacter F) (q : ℕ)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (abv : AbsoluteValue F.Carrier ℝ) (ϖ : F.Carrierˣ)
    (μ : letI := F.canonicalTopologicalData.topology
      letI := borel (LeftUnipotentQuotient n F.Carrier)
      Measure (LeftUnipotentQuotient n F.Carrier)),
    IsUnramifiedGenericConstituent F ψ π χ → IsUnramifiedGenericConstituent F ψ σ χ' →
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.valuativeRel
    letI := F.canonicalTopologicalData.localField
    letI := borel F.Carrier
    letI := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
    letI : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (upperUnipotent (n + 1) F.Carrier)
    letI : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient n F.Carrier)
    letI := borel (LeftUnipotentQuotient 0 F.Carrier)
    IsJacquetNormalization q ψ abv ϖ μ →
    ∀ (ℓ : glFunctionals ψ n π) (ℓ' : glInverseFunctionals ψ n σ),
      ℓ.val ≠ 0 → ℓ'.val ≠ 0 →
      ∀ (w : SphericalTest π ℓ) (w' : SphericalTest σ ℓ'),
        ∃ c : ℝ, ∀ s : ℂ, c < s.re →
          EqualRankConverges ψ abv μ w.val.val.val w'.val.val.val
              (integerLatticeIndicator F n) s ∧
          equalRankModelIntegral ψ abv μ π σ ℓ ℓ' w.val.val w'.val.val
              (integerLatticeIndicator F n) s =
            unramifiedEulerFactor q (unramifiedClass F χ) (unramifiedClass F χ') s

/-- Jacquet–Shalika, Euler products I, Proposition (1.5)(i), printed page 507: let `π`
and `σ` be irreducible unitary generic representations of `GL_(n+1)(F)`, take a nonzero
`ψ`-Whittaker functional on `π`, a nonzero `ψ⁻¹`-Whittaker functional on `σ`, the
normalized absolute value, and any quotient measure on `N_(n+1) \ GL_(n+1)` compatible
with the normalized Haar measures. Then for all `W`, `W'` in the two Whittaker models,
every Schwartz–Bruhat `Φ` on `F^(n+1)` and every `s` with `Re s ≥ 1`, the integral
`∫ W(g) W'(g) Φ(e_(n+1) g) |det g|^s dg` converges absolutely. -/
def UnitaryEqualRankConvergenceStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (n : ℕ),
  letI := F.canonicalTopologicalData.topology
  letI := F.canonicalTopologicalData.valuativeRel
  letI := F.canonicalTopologicalData.localField
  letI := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  letI : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  letI := borel (upperUnipotent (n + 1) F.Carrier)
  letI : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  letI := borel (LeftUnipotentQuotient n F.Carrier)
  letI : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  ∀ ψ : UnitaryAdditiveCharacter F.Carrier,
    ∀ [Measure.IsMulRightInvariant (unipotentHaar F.Carrier n)],
    ∀ μ : Measure (LeftUnipotentQuotient n F.Carrier),
      IsCompatible (upperUnipotent (n + 1) F.Carrier)
        (generalLinearHaar F.Carrier n) (unipotentHaar F.Carrier n) μ →
      ∀ {V : Type uV} [AddCommGroup V] [Module ℂ V]
        {W : Type uW} [AddCommGroup W] [Module ℂ W]
        (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
        (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W),
        Whittaker.IsGeneric ψ n π → Whittaker.IsGeneric ψ n σ →
        IsUnitarizable π → IsUnitarizable σ →
        ∀ (ℓ : glFunctionals ψ n π) (ℓ' : glInverseFunctionals ψ n σ),
          ℓ.val ≠ 0 → ℓ'.val ≠ 0 →
          ∀ (f : (coefficientModel π ℓ).toSubmodule)
            (f' : (coefficientModel σ ℓ').toSubmodule)
            (Φ : SchwartzBruhat (Fin (n + 1) → F.Carrier)) (s : ℂ), 1 ≤ s.re →
            EqualRankConverges ψ (normalizedAbsoluteValue F.canonicalTopologicalData) μ
              f.val f'.val Φ s

/-- Jacquet–Shalika, Euler products I, Proposition (1.5)(ii), printed pages 507–510: for
`π`, `σ`, the functionals and the measure as in `UnitaryEqualRankConvergenceStatement`,
every nonzero `W` in the `ψ`-Whittaker model of `π` and every `s` with `Re s ≥ 1`, there
are `W'` in the `ψ⁻¹`-Whittaker model of `σ` and a Schwartz–Bruhat `Φ` with
`Ψ(s, W, W', Φ) ≠ 0`. -/
def UnitaryEqualRankNonvanishingStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (n : ℕ),
  letI := F.canonicalTopologicalData.topology
  letI := F.canonicalTopologicalData.valuativeRel
  letI := F.canonicalTopologicalData.localField
  letI := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  letI : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  letI := borel (upperUnipotent (n + 1) F.Carrier)
  letI : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  letI := borel (LeftUnipotentQuotient n F.Carrier)
  letI : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  ∀ ψ : UnitaryAdditiveCharacter F.Carrier,
    ∀ [Measure.IsMulRightInvariant (unipotentHaar F.Carrier n)],
    ∀ μ : Measure (LeftUnipotentQuotient n F.Carrier),
      IsCompatible (upperUnipotent (n + 1) F.Carrier)
        (generalLinearHaar F.Carrier n) (unipotentHaar F.Carrier n) μ →
      ∀ {V : Type uV} [AddCommGroup V] [Module ℂ V]
        {W : Type uW} [AddCommGroup W] [Module ℂ W]
        (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
        (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W),
        Whittaker.IsGeneric ψ n π → Whittaker.IsGeneric ψ n σ →
        IsUnitarizable π → IsUnitarizable σ →
        ∀ (ℓ : glFunctionals ψ n π) (ℓ' : glInverseFunctionals ψ n σ),
          ℓ.val ≠ 0 → ℓ'.val ≠ 0 →
          ∀ f : (coefficientModel π ℓ).toSubmodule, f.val ≠ 0 →
          ∀ s : ℂ, 1 ≤ s.re →
            ∃ (f' : (coefficientModel σ ℓ').toSubmodule)
              (Φ : SchwartzBruhat (Fin (n + 1) → F.Carrier)),
              equalRankModelIntegral ψ (normalizedAbsoluteValue F.canonicalTopologicalData)
                μ π σ ℓ ℓ' f f' Φ s ≠ 0

/-- The equal-rank results of Jacquet–Shalika, Euler products I: Proposition (1.5)(i)–(ii)
for unitary generic pairs and Proposition (2.3) for unramified generic pairs. -/
def EqualRankEulerStatement : Prop :=
  UnitaryEqualRankConvergenceStatement.{uF, uV, uW} ∧
    UnitaryEqualRankNonvanishingStatement.{uF, uV, uW} ∧
    UnramifiedGenericEqualRankIntegralStatement.{uF, uV, uW}

end Langlands.RankinSelberg
