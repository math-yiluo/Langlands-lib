# Functoriality of relative normalization

Module `StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Functorial`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

A commutative square between quasi-compact, quasi-separated morphisms of schemes induces a canonical map between their relative normalizations.

For fᵢ : Yᵢ ⟶ Xᵢ with maps Y₂ ⟶ Y₁ and X₂ ⟶ X₁ giving the square, `Scheme.Hom.normalizationMap` maps the normalization of f₂ to that of f₁. `Scheme.Hom.normalizationMap_fromNormalization` proves compatibility with the maps to X₂ and X₁.

The construction pulls the first relative normalization back to X₂, uses the universal property of the second relative normalization to map into that pullback, then projects to the first normalization.

The module docstring also announces compatibility with the maps from Y₂ and Y₁ and a uniqueness statement, which are not in the file.

Reference is Stacks Project Tag 035J.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [035J](https://stacks.math.columbia.edu/tag/035J) | `normalizationMap` | canonical morphism |
| [035J](https://stacks.math.columbia.edu/tag/035J) | `normalizationMap_fromNormalization` | lower square |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Morphisms/Normalization/Functorial.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 4 declarations of the source file 2 are kept. The 2 left out are not needed by the results for which the extract is made: `AlgebraicGeometry.Scheme.Hom.normalizationMap_unique`, `AlgebraicGeometry.Scheme.Hom.toNormalization_normalizationMap`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
