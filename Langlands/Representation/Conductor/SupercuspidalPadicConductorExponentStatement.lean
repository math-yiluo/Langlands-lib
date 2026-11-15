import Langlands.LocalField.Canonical
import Langlands.Representation.Classification.Supercuspidal
import Langlands.Representation.Conductor.EssentialStatement

/-!
# The JPSS conductor theorem for supercuspidal representations of p-adic fields

Jacquet, Piatetski-Shapiro and Shalika 1981, Theorem (5.1)(i)-(iii) (printed page 211),
restricted to supercuspidal representations of `GL_(n+1)(K)` with `K` a p-adic field.
The binders and the conclusion are those of `Conductor.ConductorExponentStatement`,
with the field `K.Carrier` of a p-adic field `K`, carrying its canonical topology,
valuation and local-field structure, in place of an arbitrary nonarchimedean local
field, and with the added hypothesis `GeneralLinear.IsSupercuspidal π`.
-/

noncomputable section

namespace Langlands.Conductor

open Langlands.GeneralLinear Langlands.Whittaker Langlands.HarmonicAnalysis
open Langlands.RankinSelberg MeasureTheory
open Langlands.GeneralLinear.Iwasawa

universe uF uV

/-- JPSS 1981, Theorem (5.1)(i)-(iii) (printed page 211), for supercuspidal
representations over p-adic fields. Let `K` be a p-adic field with its canonical
topology, valuation and local-field structure. Let `q` be the residue cardinality,
`abv` the normalized absolute value, `ψ` of conductor `O` and `ν` self-dual for `ψ`.
For an irreducible admissible generic representation `π` of `GL_(n+1)(K)` that is
supercuspidal, the epsilon factor of `π` against the trivial character of `GL_1` is
`c q^(-ms)` with `m` a natural number, the vectors fixed by the level-`m` subgroup
`K_(n+1)(m)` form a line, and no lower level fixes a nonzero vector. -/
def SupercuspidalPadicConductorExponentStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : PadicField.{uF} p),
    letI := K.canonicalTopologicalData.topology
    letI := K.canonicalTopologicalData.valuativeRel
    letI := K.canonicalTopologicalData.localField
    ∀ [T2Space K.Carrier] [TotallyDisconnectedSpace K.Carrier]
      [MeasurableSpace K.Carrier] [BorelSpace K.Carrier]
      [MeasurableSpace (Langlands.GeneralLinear 1 K.Carrier)]
      [BorelSpace (Langlands.GeneralLinear 1 K.Carrier)]
      [MeasurableSpace (upperUnipotent 1 K.Carrier)]
      [BorelSpace (upperUnipotent 1 K.Carrier)]
      [MeasurableSpace (LeftUnipotentQuotient 0 K.Carrier)]
      [BorelSpace (LeftUnipotentQuotient 0 K.Carrier)]
      (q : ℕ), q = Nat.card (IsLocalRing.ResidueField (ValuativeRel.valuation K.Carrier).integer) →
    ∀ (abv : AbsoluteValue K.Carrier ℝ) (ϖ : K.Carrierˣ),
      IsUniformizingElement (ValuativeRel.valuation K.Carrier) ϖ →
      abv (ϖ : K.Carrier) = (q : ℝ)⁻¹ →
      (∀ x : K.Carrier, ValuativeRel.valuation K.Carrier x = 1 → abv x = 1) →
    ∀ ψ : UnitaryAdditiveCharacter K.Carrier, HasIntegerConductor ψ →
    ∀ ν : AdditiveHaarMeasure K.Carrier, IsSelfDual ψ ν →
    ∀ (n : ℕ) {V : Type uV} [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ (Langlands.GeneralLinear (n + 1) K.Carrier) V),
      IsGeneric ψ n π → IsSupercuspidal π →
      ∃ (c : ℂˣ) (m : ℕ),
        IsPairEpsilonFactor q ψ abv ν π (rankOneCharacter 1) (c, (m : ℤ)) ∧
        IsNewvectorConductor π m ∧
        Module.finrank ℂ (levelFixedVectors π m) = 1

end Langlands.Conductor
