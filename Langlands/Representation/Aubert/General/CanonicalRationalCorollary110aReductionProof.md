# Proof of the reduction of canonical Corollaire 1.10 (a)

This module proves the published proposition
`Langlands.Aubert.General.RationalPointFamily.CanonicalRationalCorollary110aReductionStatement`
(module `CanonicalRationalTheorem17ReductionStatements`) at universes `u`, `v`:

`theorem canonicalRationalCorollary110aReduction :
  CanonicalRationalCorollary110aReductionStatement.{u, v}`.

That is, induced K0 Weyl conjugacy
(`RationalInducedK0WeylConjugacyStatement.{u, v}`, Aubert (1995), identity
(1.2)) implies `CanonicalRationalCorollary110aStatement.{u, v}`, Corollaire
1.10 (a) for the canonical actual families. The statement module's Markdown
describes the statement, its meaning and its provenance. This file describes
only the Lean proof. The proof uses no hypothesis beyond the statement's
single input.

Authors: Worker 29, with Worker 3640 (Task 3640, block (v)). Submitted by
Worker 445 for Task 6791 (`ce46c4d1-cbcc-4f90-9681-ddce96512d23`).

## Proof

The tactic proof introduces `hWeyl : RationalInducedK0WeylConjugacyStatement.{u, v}`, then:

1. The published `rationalCorollary110aStatement_of_inducedK0WeylConjugacy`
   (`RationalCorollary110aAssembly`) is applied to `hWeyl`. This gives
   `RationalCorollary110aStatement.{u, v}`.
2. The sixth conjunct `.2.2.2.2.2.1` of `canonicalRationalTargetBridges`
   (`CanonicalRationalTargetBridgesProof`) turns this into the canonical
   target `CanonicalRationalCorollary110aStatement.{u, v}`.

All modules named are in `Langlands/Representation/Aubert/General/`.

## Dependency status

Every module this proof imports is in the Library (checked at Library commit
`f22cb810d733066a219c9a7db2ea38892a973f85`). That includes the statement
module, `RationalCorollary110aAssembly` and `CanonicalRationalTargetBridgesProof`,
the proof of Task 6316 (`4320e0f3-a054-4148-bc31-69a2529b0d13`). Against that
Library, in environment `5c94c648-e8dc-4002-a50a-071ebf3f6096`, the module
compiles with zero errors and zero warnings. The theorem uses only the axioms
`propext`, `Classical.choice` and `Quot.sound`.
