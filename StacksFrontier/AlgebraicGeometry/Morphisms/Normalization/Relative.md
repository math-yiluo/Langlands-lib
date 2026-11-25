# The universal property of relative normalization

Module `StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Relative`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For a quasi-compact, quasi-separated scheme morphism f : Y ⟶ X, Mathlib’s relative normalization factors f through `f.normalization`. The map `f.toNormalization` from Y is dominant, and `f.fromNormalization` to X is integral.

- `Scheme.Hom.normalization_universalProperty_iff_existsUnique_iso` takes a factorization of f through Z integral over X. It equates the existence of a unique compatible map from Z to each integral factorization with the existence of a unique isomorphism Z ≅ `f.normalization` compatible with both structure maps.
- `Scheme.Hom.normalizationDesc_universalProperty` takes a factorization Y ⟶ Z ⟶ X with Z integral over X. It equips `f.normalization` with its map to Z and proves the relative normalization universal property for Y ⟶ Z.

The proofs use `normalizationDesc` and its two compatibility equations to construct the maps. Uniqueness follows from `normalization.hom_ext`.

The module docstring also announces that normalizing a relative normalization again in the same source changes nothing; that result is not in the file.

References are Stacks Project Tag 035I for the universal property and Tag 035L for dominance; the docstring also cites Tag 0BXA, for the iterated normalization.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [035I](https://stacks.math.columbia.edu/tag/035I) | `normalization_universalProperty_iff_existsUnique_iso` | universal_property |
| [035I](https://stacks.math.columbia.edu/tag/035I) | `normalizationDesc_universalProperty` | normalization_over_intermediate |
| [035I](https://stacks.math.columbia.edu/tag/035I) | `AlgebraicGeometry.Scheme.Hom.instIsIntegralHomFromNormalization` | integral |
| [035I](https://stacks.math.columbia.edu/tag/035I) | `AlgebraicGeometry.Scheme.Hom.instIsDominantToNormalization` | dominant |
| [035L](https://stacks.math.columbia.edu/tag/035L) | `AlgebraicGeometry.Scheme.Hom.instIsDominantToNormalization` | dominance |
| [035I](https://stacks.math.columbia.edu/tag/035I) | `AlgebraicGeometry.Scheme.Hom.normalizationDesc` | universal_property |
| [035I](https://stacks.math.columbia.edu/tag/035I) | `AlgebraicGeometry.Scheme.Hom.toNormalization_normalizationDesc` | universal_property |
| [035I](https://stacks.math.columbia.edu/tag/035I) | `AlgebraicGeometry.Scheme.Hom.normalizationDesc_comp` | universal_property |
| [035I](https://stacks.math.columbia.edu/tag/035I) | `AlgebraicGeometry.Scheme.Hom.normalization.hom_ext` | universal_property |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Morphisms/Normalization/Relative.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 4 declarations of the source file 3 are kept. The 1 left out are not needed by the results for which the extract is made: `AlgebraicGeometry.Scheme.Hom.normalization_fromNormalization_isIso`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
