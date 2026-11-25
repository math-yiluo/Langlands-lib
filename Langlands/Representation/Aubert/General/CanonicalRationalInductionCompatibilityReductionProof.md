# Proof of the reduction of canonical induction compatibility

This module proves the published proposition
`Langlands.Aubert.General.RationalPointFamily.CanonicalRationalInductionCompatibilityReductionStatement`
(module `CanonicalRationalTheorem17ReductionStatements`) at universes `u`, `v`:

`theorem canonicalRationalInductionCompatibilityReduction :
  CanonicalRationalInductionCompatibilityReductionStatement.{u, v}`.

That is, induced K0 Weyl conjugacy
(`RationalInducedK0WeylConjugacyStatement.{u, v}`, Aubert (1995), identity
(1.2)) implies `CanonicalRationalInductionCompatibilityStatement.{u, v}`, the
first equation of Théorème 1.7 (2) for the canonical actual families. The
statement module's Markdown describes the statement, its meaning and its
provenance. This file describes only the Lean proof. The proof uses no
hypothesis beyond the statement's single input.

## Proof

The tactic proof introduces `hWeyl : RationalInducedK0WeylConjugacyStatement.{u, v}`, then:

1. The published `rationalInductionCompatibility_of_expansion_and_inducedWeyl`
   (`RationalInductionK0Assembly`) is applied to the pair
   `⟨rationalGeometricK0Expansion, hWeyl⟩`. Here `rationalGeometricK0Expansion`
   (`RationalGeometricK0Expansion`) is the published proof of the geometric
   K0 expansion. This gives `RationalInductionCompatibilityStatement.{u, v}`.
2. The second conjunct `.2.1` of `canonicalRationalTargetBridges`
   (`CanonicalRationalTargetBridgesProof`) turns this into the canonical
   target `CanonicalRationalInductionCompatibilityStatement.{u, v}`.

All modules named are in `Langlands/Representation/Aubert/General/`.

## Dependency status

Every module this proof imports is in the Library (checked at Library commit
`f22cb810d733066a219c9a7db2ea38892a973f85`). That includes the statement
module and `CanonicalRationalTargetBridgesProof`, the proof of
`CanonicalRationalTargetBridgesStatement`. Against that Library the module
compiles with zero errors
and zero warnings. The theorem has universe parameters `u` and `v` and uses only
the axioms `propext`, `Classical.choice` and `Quot.sound`.

The proof leaves its one input, `RationalInducedK0WeylConjugacyStatement.{u, v}`,
as a hypothesis. It proves neither that input nor the unconditional conclusion.
