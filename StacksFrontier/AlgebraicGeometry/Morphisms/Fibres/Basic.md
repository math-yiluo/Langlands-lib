# The reduction of a scheme, and points of fibres

Module `StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.Basic`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The file describes the reduction of a scheme and records where the points of a scheme-theoretic fibre go.

`AlgebraicGeometry.isReduced_nilradical_subscheme` proves that the subscheme cut out by `Scheme.nilradical` is reduced. For a closed immersion i from a reduced scheme to W, `ker_eq_nilradical_of_support_eq_top` identifies the defining ideal sheaf with the nilradical of W if its support is all of W. On affine opens the kernel of the surjection to a reduced ring is radical, hence equals the vanishing ideal of its support.

`Scheme.Hom.stacks_apply_fiberι` says that a point of the scheme-theoretic fibre of f over y maps to y.

The module docstring also lists a result on reduced fibres under restriction to an open of the source, which the file does not contain, and names the fibre-point lemma differently from the file.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Morphisms/Fibres/Basic.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 4 declarations of the source file 3 are kept. The 1 left out are not needed by the results for which the extract is made: `AlgebraicGeometry.isReduced_fiber_comp`.
- Renamed, the source's name being declared elsewhere as well (`licenses/Stacks/STX-RENAMES.tsv.md`): `AlgebraicGeometry.Scheme.Hom.apply_fiberι` is `AlgebraicGeometry.Scheme.Hom.stacks_apply_fiberι` here.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
