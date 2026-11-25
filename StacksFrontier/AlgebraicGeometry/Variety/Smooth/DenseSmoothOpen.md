# Dense smooth opens and geometric reducedness

Module `StacksFrontier.AlgebraicGeometry.Variety.Smooth.DenseSmoothOpen`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For a reduced scheme X locally of finite type over a field k, geometric reducedness can be detected on a dense smooth open subscheme.

`AlgebraicGeometry.geometricallyReduced_iff_exists_dense_open_smooth` equates geometric reducedness of the structure morphism f with the existence of a dense open U whose structure morphism `U.ι ≫ f` is smooth. Under the same hypotheses, `smoothLocus_iff_isGeometricallyReducedAt_genericPoint` compares the two properties at the generic point of each irreducible component.

At such a point the stalk is a field, where formal smoothness and geometric reducedness are both equivalent to separability over k. The forward implication uses the smooth locus itself. For the converse, a dense open in the locally Noetherian scheme contains all component generic points, and the generic-point criterion applies to the reduced scheme.

The equivalence is Tag 056V and the first equivalence of EGA IV 17.15.12 for reduced X. The generic-point lemma gives part of SGA 3 VIB 7.8.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [056V](https://stacks.math.columbia.edu/tag/056V) | `geometricallyReduced_iff_exists_dense_open_smooth` |  |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| SGA | 3 VIB 7.8 | `smoothLocus_iff_isGeometricallyReducedAt_genericPoint` | partial |
| EGA | IV 17.15.12 | `geometricallyReduced_iff_exists_dense_open_smooth` | X reduced, 1st equiv |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Variety/Smooth/DenseSmoothOpen.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 2 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
