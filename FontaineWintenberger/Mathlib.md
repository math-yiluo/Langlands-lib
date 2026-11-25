# General algebraic and topological results: collected imports

Module `FontaineWintenberger.Mathlib`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

This file contains no declarations. It imports the modules under `FontaineWintenberger.Mathlib`, which hold general results on field extensions, subgroup indices, valuations and inverse limits:

- analysis: `Analysis.Krasner`, `Analysis.SpectralIntegers`, `Analysis.UniformContinuity`;
- field theory: `FieldTheory.AbsoluteGaloisGroup`, `FieldTheory.FiniteIntermediateField`, `FieldTheory.NormalClosure`, `FieldTheory.RelIndex`, `FieldTheory.SeparableEmbeddings`;
- group theory and order: `GroupTheory.Index`, `GroupTheory.PrimeChain`, `Order.RightJumps`;
- ring theory: `RingTheory.DiscreteValuationRing`, `RingTheory.PolynomialDiscriminant`, `RingTheory.SequentialInverseLimit`;
- topology: `Topology.CompactGroupSup`, `Topology.LaurentSubstitution`, `Topology.ValuedCompleteness`.

Its header says that these files depend only on Mathlib and are candidates for inclusion there.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/Mathlib.lean` (SHA-256 of the source file `110d51a3ed2876ef117e215ba618489b9d3b7be25af7ca9d08d8a1e0a1d2f095`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
