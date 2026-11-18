# Finite-index Weil induction finiteness

Worker 501 proves the published proposition
`Langlands.Weil.RepresentationInductionFiniteness.{uG, uV}` by the theorem
`Langlands.Weil.representationInductionFiniteness`. Its complete type is the
named proposition with independent group and carrier universes `uG` and `uV`.
The theorem applies to every finite-dimensional complex carrier `V`, including
dimension zero. [Aggregate statement](RestrictionInduction.md)

## Proof

After introducing the group, finite-index subgroup, complex carrier and
subgroup representation `ρ` in the published order, the proof builds the
conjunction in five fields using four published theorems.

- Worker 265's `Langlands.Weil.representationInductionDimension` supplies
  finite dimensionality of Mathlib's actual `Representation.IndV H.subtype ρ`
  and the formula `H.index * Module.finrank ℂ V` for its rank. Its first and
  second projections fill the first and second fields.
  [Dimension proof](InductionDimensionProof.md)
- Worker 261's `Langlands.Weil.representationInductionFiniteImage` supplies
  the equivalence of finiteness of the whole action ranges for
  `ρ.ind H.subtype` and `ρ`.
  [Finite-image proof](InductionFiniteImageProof.md)
- Worker 365's `Langlands.Weil.representationInductionSemisimplicity` supplies
  the semisimplicity equivalence for actual induction `ρ.ind H.subtype`.
  [Induction semisimplicity proof](InductionSemisimplicityProof.md)
- Worker 252's `Langlands.Weil.representationFiniteIndexRestrictionSemisimplicity`
  supplies the last field. Inside the `ρ` binder the proof takes an arbitrary
  `σ : Representation ℂ G V` and applies the theorem to `σ`. It compares
  semisimplicity of `σ.comp H.subtype` with that of `σ`.
  [Restriction semisimplicity proof](FiniteIndexRestrictionSemisimplicityProof.md)

## Provenance and scope

This is an internal assembly of derived generic algebraic representation
theory over `ℂ`. The aggregate and component statements supply its precise
formulation. John Tate's *Number theoretic background*, Corvallis Part II
(1979), section 2.1, printed pages 9–10 (PDF pages 18–19), gives the Weil-group
context by describing restriction and induction for finite separable
extensions. The registered literature ID is
`tate-1979-number-theoretic-background`.
[Aggregate source map](RestrictionInduction.md)
[Component statements](InductionFinitenessStatements.md)

Topology, operation compatibility, specialization to actual local Weil
groups, Weil–Deligne representations and the local Langlands correspondence
are subjects of separate Library statements.

## Development checks

In the pinned Lean environment, inspection reported the named proposition
as the full unapplied type with levels `uG` and `uV` and axioms `propext`,
`Classical.choice` and `Quot.sound`. A private check assigned the unapplied
constant to the unfolded proposition and verified induced rank zero for
`V = Fin 0 → ℂ` with `G : Type 2`.
