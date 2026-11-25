# Normalization from the generic-point residue fields

Module `StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Scheme`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The normalization of a scheme X is defined by relatively normalizing it in the canonical morphism from the coproduct of the spectra of the residue fields at its generic points. This construction allows X to be nonreduced.

`Scheme.normalizationScheme` and `Scheme.stacksNormalization` abbreviate that relative normalization scheme and its structural morphism to X. Both take `hX`, requiring every quasi-compact open of X to have finitely many irreducible components.

The correspondence of generic points under open restriction shows that only finitely many generic points lie in a quasi-compact open (`Scheme.finite_genericPoints_mem`), so its inverse image is a finite union of one-point spectra. This proves `Scheme.quasiCompactFromGenericPointResidueFields`. The coproduct has a disjoint affine open cover, giving `Scheme.quasiSeparatedFromGenericPointResidueFields` for every X.

The module docstring calls the morphism `normalization`. It also announces integrality of the normalization of an integral scheme, part of Tag 035Q, which is not in the file.

References are Stacks Project Tag 035N and EGA II 7.4.6 for a special case of the construction.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [035N](https://stacks.math.columbia.edu/tag/035N) | `stacksNormalization` |  |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | II 7.4.6 | `stacksNormalization` | special case |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Morphisms/Normalization/Scheme.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 7 declarations of the source file 5 are kept. The 2 left out are not needed by the results for which the extract is made: `AlgebraicGeometry.Scheme.isIntegral_genericPointResidueSpectrum`, `AlgebraicGeometry.Scheme.isIntegral_normalizationScheme`.
- Renamed, the source's name being declared elsewhere as well (`licenses/Stacks/STX-RENAMES.tsv.md`): `AlgebraicGeometry.Scheme.normalization` is `AlgebraicGeometry.Scheme.stacksNormalization` here.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- One reference to EGA or SGA, written in the source as an attribute of that library, is taken out of the Lean text and listed above.
