# The field of norms and its Galois theory: collecting module

Module `FontaineWintenberger.FieldOfNorms`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

This file contains no declarations. It imports the modules under `FontaineWintenberger.FieldOfNorms` so that a single import gives the construction of the field of norms, its structure as a local field, its functoriality, and the equivalence of separable extensions, following §§2–3 of Wintenberger's paper.

The imported modules fall into these groups:

- `Basic`: `Defs`, `Addition`, `Ring`, `Valuation`.
- `Estimates`: `FiniteLayer`, `Herbrand`, `Integral`, `Nonnormal`, `NormContinuity`, `NormEstimates`, `Prime`, `Tame`, `Topology`, `Transfer`, `Truncated`, `Wild`.
- `Functor`: `FullyFaithful`, `Galois`, `Map`, `Separable`.
- `Galois`: `AbsoluteGroup`, `Action`, `Ambient`, `Filtration`, `Ramification`, `RelAction`, `Upper`, `UpperLimit`.
- `Layers`: `Descent`, `DescentTower`, `GaloisGood`, `GoodTowers`, `NormPairs`, `RootDescent`.
- `Relative`: `ApproximateRoots`, `Category`, `Defs`, `Equivalence`, `EssImage`, `Hom`, `Krull`, `SeparablyClosed`, `UpperStage`.
- `Structure`: `Completeness`, `Laurent`, `PrecisionTower`, `Reconstruction`, `Residue`, `ResidueEmbedding`, `Truncation`, `Uniformizer`.

Reference: Wintenberger's paper, §§2–3, as cited in the file's header.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/FieldOfNorms.lean` (SHA-256 of the source file `5a4445f4a900b528c436306df364f9c2f65ad7435544fac1fdcacd09d15ccf46`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
