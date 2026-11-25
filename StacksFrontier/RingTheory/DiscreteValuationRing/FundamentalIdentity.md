# The local fundamental identity

Module `StacksFrontier.RingTheory.DiscreteValuationRing.FundamentalIdentity`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For a module-finite local map of discrete valuation rings A → B, the file relates the fraction-field degree to the ramification index and residue degree.

`ramificationIdx_mul_inertiaDeg_eq_finrank` proves [L : K] = ef for fraction fields K and L, with flatness and a faithful A-action on B. Here e is the library's `ramificationIdx A B` and f is `Ideal.inertiaDeg` of the maximal ideal of B over A.

The sum formula for primes above the maximal ideal of A has one term, at the maximal ideal of B. Localization identifies the module rank with the fraction-field degree.

The module docstring also announces two consequences over an algebraically closed residue field; they are not in the file.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/DiscreteValuationRing/FundamentalIdentity.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 3 declarations of the source file 1 are kept. The 2 left out are not needed by the results for which the extract is made: `Stacks.DiscreteValuationRing.Ramification.bijective_algebraMap_of_ramificationIdx_eq_one_of_isAlgClosed_residueField`, `Stacks.DiscreteValuationRing.Ramification.inertiaDeg_eq_one_of_isAlgClosed_residueField`.
- 1 command that is not a declaration is left out or changed with the declarations left out (`notes/reuse/stacks-extract/extract-commands.tsv.md`).
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
