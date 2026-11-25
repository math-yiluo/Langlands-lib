# Naturality of affine sheaf localization

Module `StacksFrontier.AlgebraicGeometry.Scheme.Affine.Functoriality`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For a linear map between modules over a commutative ring R, the induced map of associated sheaves on Spec R agrees with the localized linear map on stalks.

`AlgebraicGeometry.tilde.toStalk_map` identifies the map on the stalk at a prime with localization at the prime's complement.

The localized map is determined by its agreement with the original linear map on elements with denominator one. Compatibility with scalar multiplication follows by representing the scalar and module germs on a common neighbourhood, and agreement on the image of the module follows from naturality of germs applied to the global section attached to an element.

The lemma assumes the ring and modules live in the same universe. It is one of the functorial localization identifications of Tag 01HV. The tag also records Mathlib's `tilde.functor`, `tilde.toTildeΓNatIso` for the natural global-sections identification, and the left-adjoint instance. See EGA I 1.3.5, EGA II 1.4.4, EGA I 1.3.7 and EGA I 10.10.2. The module docstring also announces the same statement for sections over a standard open, which the file does not contain.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [01HV](https://stacks.math.columbia.edu/tag/01HV) | `toStalk_map` | functorial_identifications |
| [01HV](https://stacks.math.columbia.edu/tag/01HV) | `AlgebraicGeometry.tilde.functor` | functorial_identifications |
| [01HV](https://stacks.math.columbia.edu/tag/01HV) | `AlgebraicGeometry.tilde.toOpen_map_app` | functorial_identifications |
| [01HV](https://stacks.math.columbia.edu/tag/01HV) | `AlgebraicGeometry.tilde.toTildeΓNatIso` | functorial_identifications |
| [01HV](https://stacks.math.columbia.edu/tag/01HV) | `AlgebraicGeometry.instIsLeftAdjointModuleCatCarrierModulesSpecFunctor` | tilde_exact |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | I 1.3.5 | `AlgebraicGeometry.tilde.functor` |  |
| EGA | II 1.4.4 | `AlgebraicGeometry.tilde.functor` | partial |
| EGA | I 1.3.7 | `AlgebraicGeometry.tilde.toTildeΓNatIso` |  |
| EGA | I 10.10.2 | `AlgebraicGeometry.tilde.toTildeΓNatIso` | (i), special case |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Scheme/Affine/Functoriality.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 8 declarations of the source file 7 are kept. The 1 left out are not needed by the results for which the extract is made: `AlgebraicGeometry.tilde.basicOpen_map`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 4 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
