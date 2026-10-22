import Langlands.Representation.RankinSelberg.PadicPairFactors
import Langlands.Representation.Twist.Definitions

/-!
# Unramified twists of pair factors

Henniart 1993, §4.4 (printed page 349): twisting one member of a pair by the
unramified character `|det|^u` shifts the epsilon factor of the pair from `s`
to `s + u`. The same shift holds for the L-factor, by the substitution
`W'(h) ↦ W'(h) |det h|^u` in the Rankin-Selberg integrals of JPSS 1983.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear Polynomial

universe uF uV uW

/-- Twisting either member of a pair by `|det|^u`, `u ∈ ℂ`, shifts its
L-factor from `s` to `s + u`: if `L(s, π × σ) = 1 / P(q^(-s))`, then
`L(s, π × σ ⊗ |det|^u)` and `L(s, π ⊗ |det|^u × σ)` both equal
`1 / P(q^(-u) q^(-s))`. The pair is read with the larger rank first, as in
JPSS (2.12). -/
def UnramifiedTwistLFactorStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    (r t : ℕ) {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F.Carrier) W)
    (u : ℂ) (χ : F.Carrierˣ →* ℂˣ),
    (∀ x : F.Carrierˣ,
      (χ x : ℂ) = ((F.canonicalTopologicalData.normalizedAbs (x : F.Carrier) : ℝ) : ℂ) ^ u) →
    ∀ P : ℂ[X], IsPadicSymmetricLPolynomial F ψ ν.val π σ P →
      IsPadicSymmetricLPolynomial F ψ ν.val π (Langlands.twist (χ.comp determinant) σ)
          (P.comp (C ((F.canonicalTopologicalData.residueCardinality : ℂ) ^ (-u)) * X)) ∧
        IsPadicSymmetricLPolynomial F ψ ν.val (Langlands.twist (χ.comp determinant) π) σ
          (P.comp (C ((F.canonicalTopologicalData.residueCardinality : ℂ) ^ (-u)) * X))

/-- Henniart 1993, §4.4 (printed page 349). Twisting either member of a pair
by `|det|^u`, `u ∈ ℂ`, shifts its epsilon factor from `s` to `s + u`: if
`ε(s, π × σ, ψ) = c q^(-ms)`, then `ε(s, π × σ ⊗ |det|^u, ψ)` and
`ε(s, π ⊗ |det|^u × σ, ψ)` both equal `(c q^(-mu)) q^(-ms)`. -/
def UnramifiedTwistEpsilonStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    (r t : ℕ) {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F.Carrier) W)
    (u : ℂ) (χ : F.Carrierˣ →* ℂˣ),
    (∀ x : F.Carrierˣ,
      (χ x : ℂ) = ((F.canonicalTopologicalData.normalizedAbs (x : F.Carrier) : ℝ) : ℂ) ^ u) →
    ∀ e : ℂˣ × ℤ, IsPadicSymmetricEpsilonFactor F ψ ν.val π σ e →
      ∃ e' : ℂˣ × ℤ, e'.2 = e.2 ∧
        (e'.1 : ℂ) = (e.1 : ℂ) *
          (F.canonicalTopologicalData.residueCardinality : ℂ) ^ (-((e.2 : ℂ) * u)) ∧
        IsPadicSymmetricEpsilonFactor F ψ ν.val π (Langlands.twist (χ.comp determinant) σ) e' ∧
        IsPadicSymmetricEpsilonFactor F ψ ν.val (Langlands.twist (χ.comp determinant) π) σ e'

/-- The unramified-twist relations of pair factors: the L-factor and the epsilon
factor of a pair with one member twisted by `|det|^u` are those of the pair at
`s + u`. -/
def UnramifiedTwistStatement : Prop :=
  UnramifiedTwistLFactorStatement.{uF, uV, uW} ∧ UnramifiedTwistEpsilonStatement.{uF, uV, uW}

end Langlands.RankinSelberg
