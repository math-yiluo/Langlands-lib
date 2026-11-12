import Langlands.Representation.Conductor.EssentialStatement

/-!
# Minimality of the conductor and the scaled identity at the conductor level

Jacquet, Piatetski-Shapiro and Shalika 1981, end of the proof of Theorem (5.1),
printed pages 213–214: if `c q^(-ms)` is the epsilon factor of `π` and `W₁` is a
vector of the Whittaker model fixed by `K_r(u)`, `u ≥ 0`, then `W₁ ≠ 0` forces
`u ≥ m` (Theorem (5.1)(iii), printed page 211), and for `u = m` the spherical
transform of `W₁` is a constant, so its corank-one integrals are one constant times
`∏ P_π(x_i q^(-s))⁻¹`. The final appeal to the uniqueness clause of Theorem (4.1)
is not part of the statement.
-/

noncomputable section

namespace Langlands.Conductor

open Langlands.GeneralLinear Langlands.Whittaker Langlands.HarmonicAnalysis
open Langlands.RankinSelberg MeasureTheory Polynomial

universe uF uV

/-- JPSS 1981, proof of Theorem (5.1), printed pages 213–214 (from "Soit maintenant
`u` un entier" to "P est une constante"), in rank `r = n + 2`. Under Jacquet's
normalizations `h`, with `ν` self-dual for `ψ`, let `π` be an irreducible admissible
generic representation of `GL_(n+2)(F)`, `ℓ` a nonzero `ψ`-Whittaker functional,
`L(s, π × 1) = P(q^(-s))⁻¹`, and `c q^(-ms)` (`m : ℤ`) the epsilon factor of `π`
against the trivial character of `GL_1`. For every vector `v` of the model of `ℓ`
fixed by `K_(n+2)(u)`: if `v ≠ 0` then `m ≤ u`; and if `u = m` there is one
constant `C` with `Ψ(s, v, W(x; ψ̄)) = C ∏ i, P(x_i q^(-s))⁻¹` for every `x`. -/
def ConductorMinimalityStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [T2Space F] [TotallyDisconnectedSpace F]
    [MeasurableSpace F] [BorelSpace F] (n : ℕ)
    [MeasurableSpace (Langlands.GeneralLinear (n + 1) F)]
    [BorelSpace (Langlands.GeneralLinear (n + 1) F)]
    [MeasurableSpace (upperUnipotent (n + 1) F)] [BorelSpace (upperUnipotent (n + 1) F)]
    [MeasurableSpace (LeftUnipotentQuotient n F)] [MeasurableSpace (LeftUnipotentQuotient 0 F)]
    [MeasurableSpace (Langlands.GeneralLinear 1 F)] [BorelSpace (Langlands.GeneralLinear 1 F)]
    [MeasurableSpace (upperUnipotent 1 F)] [BorelSpace (upperUnipotent 1 F)]
    (q : ℕ) (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ) (ϖ : Fˣ)
    (μ : Measure (LeftUnipotentQuotient n F)) (h : IsJacquetNormalization q ψ abv ϖ μ)
    (ν : AdditiveHaarMeasure F), IsSelfDual ψ ν →
    ∀ {V : Type uV} [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ (Langlands.GeneralLinear ((n + 1) + 1) F) V),
      IsGeneric ψ (n + 1) π →
      ∀ ℓ : glFunctionals ψ (n + 1) π, ℓ.val ≠ 0 →
      ∀ P : ℂ[X], IsCharacterLPolynomial q ψ abv (rankOneQuotientHaar F) 1 π P →
      ∀ (c : ℂˣ) (m : ℤ),
        IsPairEpsilonFactor q ψ abv ν π (rankOneCharacter 1) (c, m) →
      ∀ (u : ℕ) (v : (coefficientModel π ℓ).toSubmodule),
        v ∈ levelFixedVectors (V := (coefficientModel π ℓ).toSubmodule)
          (modelRepresentation π ℓ) u →
        (v ≠ 0 → m ≤ (u : ℤ)) ∧
        ((u : ℤ) = m → ∃ C : ℂ, ∀ x : Fin (n + 1) → ℂˣ,
          (∃ a : ℝ, ∀ s : ℂ, a < s.re →
            CorankOneConverges ψ abv μ v.val
              (inverseSphericalWhittaker h.conductor.1 h.uniformizer q x) s) ∧
          HasRationalContinuation q
            (corankOneIntegral ψ abv μ v.val
              (inverseSphericalWhittaker h.conductor.1 h.uniformizer q x))
            (C • essentialFactor P x))

end Langlands.Conductor
