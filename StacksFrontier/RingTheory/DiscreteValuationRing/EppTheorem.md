# Epp’s elimination of ramification

Module `StacksFrontier.RingTheory.DiscreteValuationRing.EppTheorem`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For an extension A → B of discrete valuation rings with fraction fields K and L, the file proves the existence of a finite base change that eliminates the ramification indices.

`exists_finite_extension_isWeakSolution` produces a finite extension K₁/K and an integral-closure base-change package whose ramification indices at all maximal ideals are one. The input `hEpp` supplies `EppCondition A B p` in positive residue characteristic p, requiring separability of the upper perfect-core elements over the lower residue field. `eppTheorem_monomorphic` states this result as the library’s Epp theorem proposition in one universe.

Residue characteristic zero uses the tame or characteristic-zero theorem. In positive residue characteristic, Epp’s condition passes to the completions. The complete equal-characteristic theorem gives a weak solution with the uniformizer-root data needed for Kummer descent. In mixed characteristic, separability enables ordinary completion descent.

All input rings and fields, the solution field, and the package carriers lie in one universe.

The existence theorem is Tag 09F9.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [09F9](https://stacks.math.columbia.edu/tag/09F9) | `exists_finite_extension_isWeakSolution` |  |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/DiscreteValuationRing/EppTheorem.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
