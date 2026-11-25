# Étaleness on affine neighbourhoods

Module `StacksFrontier.AlgebraicGeometry.Morphisms.Etale.Defs`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The file defines étaleness at a source point and relates it to Mathlib’s global property `Etale`.

`EtaleAt f x` is the library’s abbreviation for the existence of affine opens U around x and V in the target with U contained in the inverse image of V and with étale coordinate ring map `f.appLE V U`. `etale_iff_forall_etaleAt` identifies `Etale f` with this condition at every source point, using the affine-local criterion for ring properties.

The module docstring also lists two results turning étaleness of a map on sections, or at a point, into étaleness of a morphism of schemes; the file does not contain them.

Tag 02GI, for the pointwise and global notions. SGA 1 IX 1.1.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [02GI](https://stacks.math.columbia.edu/tag/02GI) | `EtaleAt` | etale_at_point |
| [02GI](https://stacks.math.columbia.edu/tag/02GI) | `AlgebraicGeometry.Etale` | etale_morphism |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| SGA | 1 IX 1.1 | `EtaleAt` |  |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Morphisms/Etale/Defs.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 4 declarations of the source file 2 are kept. The 2 left out are not needed by the results for which the extract is made: `AlgebraicGeometry.etale_resLE_of_appLE_etale`, `AlgebraicGeometry.exists_isAffineOpen_etale_comp_ι_of_etaleAt`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- One reference to EGA or SGA, written in the source as an attribute of that library, is taken out of the Lean text and listed above.
