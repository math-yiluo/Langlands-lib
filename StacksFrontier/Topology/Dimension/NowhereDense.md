# Nowhere dense closed subsets of a Noetherian space

Module `StacksFrontier.Topology.Dimension.NowhereDense`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

In a Noetherian space X, a closed subset S is nowhere dense exactly when it contains no irreducible component of X: this is `IsClosed.isNowhereDense_iff_forall_irreducibleComponents_not_subset`.

One direction is the private `IsNowhereDense.false_of_subset_irreducibleComponent`: every irreducible component of a Noetherian space contains a nonempty open subset of X, so a component inside S would give S nonempty interior. Conversely, if S has a point x in its interior, the irreducible component through x lies in the closure of its intersection with that interior, hence in the closed set S.

The module docstring is organised around the bound dim S + 1 ≤ dim X for a nowhere dense closed S and its variants; none of them is in the file.

The component-interior fact is cited as Tag 0052 (3).

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/Topology/Dimension/NowhereDense.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 13 declarations of the source file 2 are kept. The 11 left out are not needed by the results for which the extract is made; `licenses/Stacks/STX-MANIFEST.tsv.md` lists them.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
