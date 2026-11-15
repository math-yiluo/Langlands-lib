# Proof of the reduction of canonical involutivity

This module proves the published proposition
`Langlands.Aubert.General.RationalPointFamily.CanonicalRationalInvolutivityReductionStatement`
(module `CanonicalRationalTheorem17ReductionStatements`) at universes `u`, `v`:

`theorem canonicalRationalInvolutivityReduction :
  CanonicalRationalInvolutivityReductionStatement.{u, v}`.

That is, induced K0 Weyl conjugacy
(`RationalInducedK0WeylConjugacyStatement.{u, v}`, Aubert (1995), identity
(1.2)) implies `CanonicalRationalInvolutivityStatement.{u, v}`, Théorème 1.7
(3) (`D ∘ D = id` on exact K0) for the canonical actual operator. The
statement module's Markdown describes the statement, its meaning and its
provenance. This file describes only the Lean proof. The proof uses no
hypothesis beyond the statement's single input.

Authors: Worker 29, with Worker 3640 (Task 3640, block (v)). Submitted by
Worker 432 for Task 6790 (`b282bbd4-446d-476a-9bfc-18ec1cef2839`).

## Proof

The tactic proof introduces `hWeyl : RationalInducedK0WeylConjugacyStatement.{u, v}`, then:

1. The published `rationalInvolutivityStatement_of_inducedK0WeylConjugacy`
   (`RationalTermTransitivityProof`) is applied to `hWeyl`. This gives
   `RationalInvolutivityStatement.{u, v}`.
2. The fourth conjunct `.2.2.2.1` of `canonicalRationalTargetBridges`
   (`CanonicalRationalTargetBridgesProof`) turns this into the canonical
   target `CanonicalRationalInvolutivityStatement.{u, v}`.

All modules named are in `Langlands/Representation/Aubert/General/`.

## Dependency status

Every module this proof imports is in the Library (checked at Library commit
`f22cb810d733066a219c9a7db2ea38892a973f85`). That includes the statement
module and `CanonicalRationalTargetBridgesProof`, the proof of Task 6316
(`4320e0f3-a054-4148-bc31-69a2529b0d13`). Against that Library the module
compiles with zero errors and zero warnings. The theorem has level parameters
`u` and `v` and uses only the axioms `propext`, `Classical.choice` and
`Quot.sound`.
