# Base change of adic formal smoothness

Module `StacksFrontier.RingTheory.FormallySmooth.BaseChange`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The power-kernel lifting property for an adic ideal survives arbitrary extension of the base ring.

`RingHom.FormallySmoothNAdic.baseChange` takes commutative R-algebras S and R′ and an ideal n of S. If R → S is formally smooth for the n-adic topology, the map from R′ to the tensor product of S and R′ over R is formally smooth for the extended ideal. The map from R′ is `Algebra.TensorProduct.includeRight`, and n is extended along `Algebra.TensorProduct.includeLeft`, the canonical factor maps.

For a lifting problem over R′, restrict the map into the square-zero quotient to S. The power-kernel condition descends along the canonical map from S since extension of ideals commutes with powers. Lift the restricted map over R, then combine it with the given map from R′ by the tensor product’s universal property.

Stacks Project, Tag 07EG. EGA 0 19.3.5 (iii) and 0 19.9.3 for the adic case.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [07EG](https://stacks.math.columbia.edu/tag/07EG) | `baseChange` |  |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | 0 19.3.5 | `baseChange` | (iii) |
| EGA | 0 19.9.3 | `baseChange` | adic topology case |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/FormallySmooth/BaseChange.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 2 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
