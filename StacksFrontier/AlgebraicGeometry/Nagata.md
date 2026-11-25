# Nagata schemes

Module `StacksFrontier.AlgebraicGeometry.Nagata`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The file defines Nagata schemes by testing rings of sections on affine neighbourhoods.

`IsNagataScheme X` is defined for any scheme `X`. Each point must lie in an affine open whose section ring satisfies `StacksIsNagataRing`, StacksFrontier’s own predicate for Nagata rings.

The module docstring also announces Japanese schemes; that definition is not in this file.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Nagata.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 2 declarations of the source file 1 are kept. The 1 left out are not needed by the results for which the extract is made: `IsJapaneseScheme`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
