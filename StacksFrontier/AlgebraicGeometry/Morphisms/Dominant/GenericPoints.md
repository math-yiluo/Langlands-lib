# Dominance tested at generic points

Module `StacksFrontier.AlgebraicGeometry.Morphisms.Dominant.GenericPoints`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The file shows that a quasi-compact scheme morphism is dominant exactly when its image contains the generic point of every irreducible component of the target.

`exists_open_nhds_disjoint_range_of_quasiCompact` gives an open neighbourhood with empty inverse image for a target generic point outside the image of a quasi-compact morphism. Its proof works over an affine neighbourhood, using quasi-compactness to represent the preimage as the image of an affine scheme. In the resulting ring map, a minimal prime in the closure of the image is minimal over the kernel and is the contraction of a prime of the target ring.

`isDominant_iff_genericPoints_subset_range` applies this separation result to a dominant quasi-compact morphism. The reverse implication uses density of the set `genericPoints` of generic points of irreducible components.

The module docstring also lists a version of the test for a source with finitely many irreducible components, and two results that go with it; the file does not contain them.

Tag 02NE for separation, with the more general EGA IV 9.7.5.1. Tag 01RL for the quasi-compact criterion, with EGA IV 1.1.5 (equivalence of a and b) and EGA I 6.6.5.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [02NE](https://stacks.math.columbia.edu/tag/02NE) | `exists_open_nhds_disjoint_range_of_quasiCompact` |  |
| [01RL](https://stacks.math.columbia.edu/tag/01RL) | `isDominant_iff_genericPoints_subset_range` |  |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | IV 9.7.5.1 | `exists_open_nhds_disjoint_range_of_quasiCompact` | more general |
| EGA | IV 1.1.5 | `isDominant_iff_genericPoints_subset_range` | a) <=> b) |
| EGA | I 6.6.5 | `isDominant_iff_genericPoints_subset_range` |  |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Morphisms/Dominant/GenericPoints.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 14 declarations of the source file 10 are kept. The 4 left out are not needed by the results for which the extract is made: `AlgebraicGeometry.finite_irreducibleComponents_of_isDominant`, `AlgebraicGeometry.iUnion_closure_genericPoint_eq_univ`, `AlgebraicGeometry.iUnion_closure_image_genericPoints_eq_univ`, `AlgebraicGeometry.isDominant_iff_genericPoint_mem_range`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 3 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
