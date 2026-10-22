import Langlands.Representation.Conductor.Essential
import Langlands.Representation.RankinSelberg.EpsilonFactor

/-!
# Existence of the essential vector and the conductor exponent

Jacquet 2012, Theorem 1 (printed page 517), with the uniqueness clause after it:
an irreducible admissible generic representation of `GL_(n+2)(F)` has exactly one
essential vector in each Whittaker model. Jacquet, Piatetski-Shapiro and Shalika
1981, Theorem (5.1) (printed page 211), whose proof uses that existence result: the
exponent `m` of the epsilon factor `c q^(-ms)` is a natural number, the level-`m`
fixed space of `GL_r(F)` is a line, every lower level has no nonzero fixed
vector, and the essential vector is fixed at level `m`.
-/

noncomputable section

namespace Langlands.Conductor

open Langlands.GeneralLinear Langlands.Whittaker Langlands.HarmonicAnalysis
open Langlands.RankinSelberg MeasureTheory Polynomial
open Langlands.GeneralLinear.Iwasawa

universe uF uV

/-- Jacquet 2012, Theorem 1 (printed page 517) and the uniqueness clause after it.
Let `F` be a nonarchimedean local field with Jacquet's normalizations `h` (residue
cardinality `q`, normalized absolute value, `ψ` of conductor `O`, quotient measure
`μ` from the Haar measures giving `GL_(n+1)(O)` and `N_(n+1)(O)` mass one). For an
irreducible admissible generic representation `π` of `GL_(n+2)(F)` and a nonzero
`ψ`-Whittaker functional `ℓ`, exactly one vector of the Whittaker model of `ℓ` is
essential. -/
def EssentialVectorStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (n : ℕ)
    [MeasurableSpace (Langlands.GeneralLinear (n + 1) F)]
    [BorelSpace (Langlands.GeneralLinear (n + 1) F)]
    [MeasurableSpace (upperUnipotent (n + 1) F)] [BorelSpace (upperUnipotent (n + 1) F)]
    [MeasurableSpace (LeftUnipotentQuotient n F)] [MeasurableSpace (LeftUnipotentQuotient 0 F)]
    [MeasurableSpace (Langlands.GeneralLinear 1 F)] [BorelSpace (Langlands.GeneralLinear 1 F)]
    (q : ℕ) (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ) (ϖ : Fˣ)
    (μ : Measure (LeftUnipotentQuotient n F)) (h : IsJacquetNormalization q ψ abv ϖ μ)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (Langlands.GeneralLinear ((n + 1) + 1) F) V),
    IsGeneric ψ (n + 1) π →
    ∀ ℓ : glFunctionals ψ (n + 1) π, ℓ.val ≠ 0 →
      ∃! w : (coefficientModel π ℓ).toSubmodule, IsEssentialVector h π ℓ w

/-- JPSS 1981, Theorem (5.1)(i)-(iii) (printed page 211), in every rank `n + 1`.
Let `q` be the residue cardinality, `abv` the normalized absolute value, `ψ` of
conductor `O` and `ν` self-dual for `ψ`. For an irreducible admissible generic
representation `π` of `GL_(n+1)(F)`, the epsilon factor of `π` against the trivial
character of `GL_1` is `c q^(-ms)` with `m` a natural number, the vectors fixed by
the level-`m` subgroup `K_(n+1)(m)` form a line, and no lower level fixes a nonzero
vector. -/
def ConductorExponentStatement : Prop :=
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
      ∃ (c : ℂˣ) (m : ℕ),
        IsPairEpsilonFactor q ψ abv ν π (rankOneCharacter 1) (c, (m : ℤ)) ∧
        IsNewvectorConductor π m ∧
        Module.finrank ℂ (levelFixedVectors π m) = 1

/-- JPSS 1981, Theorem (5.1)(ii) (printed page 211), first clause, in rank `n + 2`,
with the essential vector of Jacquet 2012, Theorem 1: under Jacquet's normalizations
`h` and with `ν` self-dual for `ψ`, if `c q^(-ms)` is the epsilon factor of an
irreducible admissible generic `π` against the trivial character of `GL_1`, then
every essential vector of a nonzero Whittaker model of `π` is fixed by the
level-`m` subgroup `K_(n+2)(m)`. -/
def EssentialVectorLevelStatement : Prop :=
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
      ∀ w : (coefficientModel π ℓ).toSubmodule, IsEssentialVector h π ℓ w →
      ∀ (c : ℂˣ) (m : ℕ),
        IsPairEpsilonFactor q ψ abv ν π (rankOneCharacter 1) (c, (m : ℤ)) →
        w ∈ levelFixedVectors (V := (coefficientModel π ℓ).toSubmodule)
          (modelRepresentation π ℓ) m

/-- The corrected essential-vector and conductor theorems: Jacquet 2012, Theorem 1
with its uniqueness clause, and JPSS 1981, Theorem (5.1). -/
def EssentialConductorStatement : Prop :=
  EssentialVectorStatement.{uF, uV} ∧ ConductorExponentStatement.{uF, uV} ∧
    EssentialVectorLevelStatement.{uF, uV}

end Langlands.Conductor
