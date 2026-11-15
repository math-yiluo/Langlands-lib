# Proof of the reduction of canonical Corollaire 1.10 (b)

This module proves the published proposition
`Langlands.Aubert.General.RationalPointFamily.CanonicalRationalCorollary110bReductionStatement`
(module `CanonicalRationalTheorem17ReductionStatements`) at universes `u`, `v`:

`theorem canonicalRationalCorollary110bReduction :
  CanonicalRationalCorollary110bReductionStatement.{u, v}`.

The statement has three inputs:

- rank-one self-association, `RationalRankOneSelfAssociationStatement.{u, v}`;
- the whole-category cuspidal decomposition of Renard VI.3.5,
  `CuspidalSupport.RationalWholeCuspidalCategoryDecompositionStatement.{u, max (u + 1) v}`;
- induced K0 Weyl conjugacy, `RationalInducedK0WeylConjugacyStatement.{u, v}`.

Together they imply `CanonicalRationalCorollary110bStatement.{u, v}`,
Corollaire 1.10 (b) for the canonical actual families. The statement module's
Markdown describes the statement, its meaning and its provenance. This file
describes only the Lean proof. The proof uses no hypothesis beyond the
statement's three inputs.

Authors: Worker 29, with Worker 3640 (Task 3640, block (v)).
Submitted unchanged in its Lean by Worker 435 under the proof task Task 6793
(`0b432fc9-0ae4-43b6-8d4a-15b489d84e32`).

## Proof

The tactic proof introduces `hSelf`, `hwhole` and `hWeyl`, in the order of
the statement's inputs, then:

1. Cuspidal Jacquet-factor extraction.
   `rationalCuspidalExtractionInputs_of_wholeStatement`
   (`RationalLeviInductionExclusionFromWhole`) turns `hwhole` into the
   extraction inputs. `rationalCuspidalJacquetFactorExtraction_of_inputs`
   (`RationalCuspidalExtractionInputs`) then gives
   `RationalCuspidalJacquetFactorExtractionStatement.{u, v}`.
2. Rank-one Jacquet modules.
   `rationalRankOneJacquetModules_of_extraction`
   (`RationalRankOneJacquetDetectionReduction`) turns step 1 into
   `RationalRankOneJacquetModulesStatement.{u, v}`.
3. `rationalCorollary110bFromRankOneInputs` (`RationalCorollary110bAssembly`)
   is applied to `hSelf`, step 2 and `hWeyl`. This gives
   `RationalCorollary110bStatement.{u, v}`.
4. The seventh conjunct `.2.2.2.2.2.2.1` of `canonicalRationalTargetBridges`
   (`CanonicalRationalTargetBridgesProof`) turns this into the canonical
   target `CanonicalRationalCorollary110bStatement.{u, v}`.

All theorems used are published. All modules named are in
`Langlands/Representation/Aubert/General/`.

## Dependency status

Every module this proof imports is in the Library (checked at Library commits
`4f4af6baed8c8e029e87c8303ea44c8f1d9f2f86` and
`f22cb810d733066a219c9a7db2ea38892a973f85`). That includes the statement
module and `CanonicalRationalTargetBridgesProof`, the proof of Task 6316
(`4320e0f3-a054-4148-bc31-69a2529b0d13`). `lean_check` of this module in
environment `5c94c648-e8dc-4002-a50a-071ebf3f6096`, over Library commit
`f22cb810d733066a219c9a7db2ea38892a973f85`, reports zero errors and zero
warnings. The theorem `canonicalRationalCorollary110bReduction` uses only the
axioms `propext`, `Classical.choice` and `Quot.sound`; its universe parameters
are `u` and `v`.
