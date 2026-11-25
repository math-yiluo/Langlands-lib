# Dominance between integral schemes

Module `StacksFrontier.AlgebraicGeometry.Morphisms.Dominant.IntegralSchemes`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For a morphism between integral schemes, dominance can be tested on generic points, affine coordinate rings or local rings.

`tfae_isDominant_of_isIntegral` packages six equivalent conditions in `List.TFAE`.

1. The morphism f is dominant.
2. It sends the generic point of the source to the generic point of the target.
3. The pullback on sections is injective for some pair of nonempty affine opens U in the source and V in the target with f(U) contained in V.
4. The pullback on sections is injective for every such pair.
5. The stalk map is injective at some source point.
6. The stalk map is injective at every source point.

The proof uses that every nonempty open of an integral scheme contains its generic point and that the stalk there is a field. `Scheme.Hom.map_genericPoint_of_injective_appLE` uses injectivity to contract the zero prime to the zero prime. The affine-neighbourhood and germ lemmas relate the tests on sections and stalks. The implication from an injective stalk map to injectivity on sections already works with an integral target and an arbitrary source.

Tag 0CC1.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [0CC1](https://stacks.math.columbia.edu/tag/0CC1) | `tfae_isDominant_of_isIntegral` |  |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Morphisms/Dominant/IntegralSchemes.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
