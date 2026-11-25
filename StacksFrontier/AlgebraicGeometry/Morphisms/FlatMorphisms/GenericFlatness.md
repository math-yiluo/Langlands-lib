# Generic flatness over a reduced base

Module `StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.GenericFlatness`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For a finite type morphism to a reduced scheme, a single dense open of the base suffices to make both the morphism and a given finite type quasi-coherent module flat and finitely presented.

`exists_dense_open_flat_finitePresentation` takes f : X ⟶ S with S reduced, f locally of finite type and quasi-compact, and a finite type quasi-coherent module F on X. It produces a dense open U of S such that f⁻¹(U) ⟶ U is flat and of finite presentation, and F restricted to f⁻¹(U) is flat over U and finitely presented as a sheaf of modules there.

Over each affine base open, the proof applies affine generic freeness simultaneously to a finite affine cover of its preimage, using the chart algebras, section modules and cyclic quotients supported on the complements of pairwise overlaps. The resulting basic opens give U, with finitely presented overlap quotients ensuring quasi-separatedness, affine tests giving flatness and local finite presentation, and fpqc descent supplying finite presentation of the restricted sheaf.

References are Stacks Project Tag 052B and the more general result EGA IV 8.9.4. The auxiliary references are EGA I 7.1.1 for finite intersections of dense opens and SGA 4 IV 8.5.5 for Zariski target coverings.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [052B](https://stacks.math.columbia.edu/tag/052B) | `exists_dense_open_flat_finitePresentation` |  |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | I 7.1.1 | `dense_sInter_of_finite` | density clause |
| SGA | 4 IV 8.5.5 | `isZariskiLocalAtTarget_quasiSeparated` | Zariski target coverings |
| EGA | IV 8.9.4 | `exists_dense_open_flat_finitePresentation` | more general |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Morphisms/FlatMorphisms/GenericFlatness.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 3 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
