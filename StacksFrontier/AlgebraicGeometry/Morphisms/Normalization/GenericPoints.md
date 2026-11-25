# Generic points and their residue-field spectra

Module `StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.GenericPoints`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The generic points of the irreducible components of a scheme determine a coproduct of residue-field spectra mapping to the scheme. This morphism is the input to the construction of absolute normalization by relative normalization.

- `Scheme.genericPointsInOpenEquiv` identifies the generic points of X lying in an open U with the generic points of U.
- `Scheme.genericPointResidueSpectrum` is the coproduct of the spectra of the residue fields at all generic points of X. `Scheme.fromGenericPointResidueFields` is the morphism obtained by assembling the canonical maps from those spectra to X. `Scheme.genericPointResidueSpectrum_ι_fromGenericPointResidueFields` computes its restriction to each summand.
- `Scheme.genericPointResidueSpectrum_finite_irreducibleComponents` proves that every quasi-compact open of the coproduct has finitely many components, for an arbitrary scheme X.

The open-subscheme equivalence uses the correspondence between components of U and components of X meeting U. Each residue-field spectrum has one point, so a quasi-compact open in their disjoint union has finitely many points. The module docstring also announces a characterization of the morphism by its restrictions and its dominance, which are not in the file.

References are Stacks Project Tag 035M for the coproduct and its map and Tag 035N for the normalization context.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [035M](https://stacks.math.columbia.edu/tag/035M) | `genericPointResidueSpectrum` | the source scheme |
| [035M](https://stacks.math.columbia.edu/tag/035M) | `fromGenericPointResidueFields` | the morphism |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Morphisms/Normalization/GenericPoints.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 10 declarations of the source file 8 are kept. The 2 left out are not needed by the results for which the extract is made: `AlgebraicGeometry.Scheme.eq_fromGenericPointResidueFields_iff`, `AlgebraicGeometry.Scheme.fromGenericPointResidueFields_isDominant`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
