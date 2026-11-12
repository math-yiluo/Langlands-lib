import Langlands.Representation.Conductor.EssentialStatement
import Langlands.Representation.RankinSelberg.PairEpsilonFactor

/-!
# Existence of the epsilon factor against the trivial character of `GL_1`

Jacquet, Piatetski-Shapiro and Shalika 1983, Theorem (2.7)(iii) (printed pages
390–391), for the pair `(π, 1)` with `1` the trivial character of `GL_1`: an
irreducible admissible generic representation `π` of `GL_(n+1)(F)` has an epsilon
factor `ε(s, π × 1, ψ) = c q^(-ms)` with `c ≠ 0` and `m` an integer, over every
nonarchimedean local field `F`.
-/

noncomputable section

namespace Langlands.Conductor

open Langlands.GeneralLinear Langlands.Whittaker Langlands.HarmonicAnalysis
open Langlands.RankinSelberg MeasureTheory
open Langlands.GeneralLinear.Iwasawa

universe uF uV

/-- JPSS 1983, Theorem (2.7)(iii), printed page 391, for `π' = 1` on `GL_1`. With the
normalizations of `ConductorExponentStatement` (`q` the residue cardinality, `abv`
normalized, `ψ` of conductor `O`, `ν` self-dual for `ψ`), every irreducible admissible
generic representation `π` of `GL_(n+1)(F)` has an epsilon factor `c q^(-ms)`,
`c : ℂˣ`, `m : ℤ`, against the trivial character of `GL_1`: the equal-rank relation
when `n = 0`, the unequal-rank relation for every block when `n ≥ 1`. -/
def TrivialCharacterEpsilonStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [T2Space F] [TotallyDisconnectedSpace F]
    [MeasurableSpace F] [BorelSpace F]
    [MeasurableSpace (Langlands.GeneralLinear 1 F)] [BorelSpace (Langlands.GeneralLinear 1 F)]
    [MeasurableSpace (upperUnipotent 1 F)] [BorelSpace (upperUnipotent 1 F)]
    [MeasurableSpace (LeftUnipotentQuotient 0 F)] [BorelSpace (LeftUnipotentQuotient 0 F)]
    (q : ℕ), q = Nat.card (IsLocalRing.ResidueField (ValuativeRel.valuation F).integer) →
    ∀ (abv : AbsoluteValue F ℝ) (ϖ : Fˣ), IsUniformizingElement (ValuativeRel.valuation F) ϖ →
      abv (ϖ : F) = (q : ℝ)⁻¹ → (∀ x : F, ValuativeRel.valuation F x = 1 → abv x = 1) →
    ∀ ψ : UnitaryAdditiveCharacter F, HasIntegerConductor ψ →
    ∀ ν : AdditiveHaarMeasure F, IsSelfDual ψ ν →
    ∀ (n : ℕ) {V : Type uV} [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V),
      IsGeneric ψ n π →
      PairEpsilonFactorExists q ψ abv ν π (rankOneCharacter 1)

end Langlands.Conductor
