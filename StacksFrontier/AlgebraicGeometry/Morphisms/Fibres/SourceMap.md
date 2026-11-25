# Functoriality of fibres in the source

Module `StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.SourceMap`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Precomposing a scheme morphism induces a map between its fibres over the same target point.

For f from X to Y, i from Z to X, and y in Y, `Scheme.Hom.stacksFiberMap` sends the fibre of `i ≫ f` at y to the fibre of f at y, over Spec κ(y): `Scheme.Hom.fiberMap_fiberι` and `Scheme.Hom.fiberMap_fiberToSpecResidueField` (with their `_assoc` forms, and the pointwise `Scheme.Hom.fiberι_fiberMap`) give its composites with the fibre inclusion and with the map to Spec κ(y). `Scheme.Hom.isPullback_fiberMap` identifies it as the base change of i along the fibre inclusion. Consequently instances carry preimmersions, open immersions and closed immersions from i to it.

The comparison is constructed by the pullback universal property, and the Cartesian square is obtained by pasting it onto the square that defines the fibre of f.

The lemma names and the module docstring call the morphism `fiberMap`. The docstring also announces a homeomorphism onto a subspace of the fibre, a formula for the range and criteria for an empty fibre, not in the file.

## References

Stacks Project, Tag 053R, for the fibre of a closed subscheme.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Morphisms/Fibres/SourceMap.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 18 declarations of the source file 10 are kept. The 8 left out are not needed by the results for which the extract is made: `AlgebraicGeometry.Scheme.Hom.fiberMapHomeo`, `AlgebraicGeometry.Scheme.Hom.fiberMapHomeo_apply`, `AlgebraicGeometry.Scheme.Hom.isEmpty_fiber_comp_iff`, `AlgebraicGeometry.Scheme.Hom.range_fiberMap`, `AlgebraicGeometry.Scheme.IdealSheafData.fiberHomeo`, `AlgebraicGeometry.Scheme.IdealSheafData.fiberHomeo_apply`, `AlgebraicGeometry.Scheme.IdealSheafData.isEmpty_fiber_comp_iff`, `AlgebraicGeometry.Scheme.IdealSheafData.range_fiberMap_subschemeι`.
- Renamed, the source's name being declared elsewhere as well (`licenses/Stacks/STX-RENAMES.tsv.md`): `AlgebraicGeometry.Scheme.Hom.fiberMap` is `AlgebraicGeometry.Scheme.Hom.stacksFiberMap` here.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
