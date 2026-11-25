# Fibre dimension under specialization

Module `StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FibreDimensionSpecialization`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For a flat morphism locally of finite presentation, the local Krull dimension of a fibre is preserved along certain specializations in the source.

`topologicalKrullDimAt_fiber_eq_of_specialization_of_mem_genericPoints` proves equality of the local fibre dimensions at `f.asFiber x'` and `f.asFiber x` if x′ specializes to x and `f.asFiber x` is generic in an irreducible component of its fibre. The proof uses `exists_open_relativeDimension_fiberwise_dense` to place x in an open of constant relative dimension. This open also contains x′.

`isNowhereDense_fiberι_preimage_iff_of_isHomeomorph` transports nowhere density in fibres across commuting homeomorphisms of source and base, for subsets corresponding under the source homeomorphism. The proof identifies the fibres homeomorphically and uses invariance of closure and interior.

Tag 054U. EGA IV 12.2.1.1 (partial).

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [054U](https://stacks.math.columbia.edu/tag/054U) | `topologicalKrullDimAt_fiber_eq_of_specialization_of_mem_genericPoints` |  |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | IV 12.2.1.1 | `topologicalKrullDimAt_fiber_eq_of_specialization_of_mem_genericPoints` | partial |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Morphisms/CohenMacaulay/FibreDimensionSpecialization.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- One reference to EGA or SGA, written in the source as an attribute of that library, is taken out of the Lean text and listed above.
