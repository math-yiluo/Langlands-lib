# Density of smooth points on fibres

Module `StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.LocusFibre`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For a flat morphism locally of finite type over a locally Noetherian base, a dense open of a fibre that is smooth over the residue field makes the smooth locus dense in that fibre.

`dense_preimage_smoothLocus_fiber_of_dense_open_smooth` assumes g : Y ⟶ S is flat and locally of finite type and S is locally Noetherian. If a dense open U of the fibre at s is smooth over κ(s) (hypothesis `hsmooth`), the inverse image of `g.smoothLocus` in that fibre is dense.

Local Noetherianness supplies local finite presentation of g, and base-change stability gives it for the fibre over κ(s). In the fibre square, flatness of g lets the smooth-locus base change theorem identify the preimage with the smooth locus of the fibre, which contains the given dense open.

The module docstring also announces two results on base change to the fraction field of a Noetherian domain; they are not in this file.

Stacks Project, Tag 02V4 and Tag 01TX.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Morphisms/Smooth/LocusFibre.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 3 declarations of the source file 1 are kept. The 2 left out are not needed by the results for which the extract is made: `AlgebraicGeometry.dense_preimage_smoothLocus_of_dense_open_smooth`, `AlgebraicGeometry.flat_Spec_map_algebraMap_of_isFractionRing`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
