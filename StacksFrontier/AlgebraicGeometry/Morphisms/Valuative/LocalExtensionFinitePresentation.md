# Extending local homomorphisms when the target is locally of finite presentation

Module `StacksFrontier.AlgebraicGeometry.Morphisms.Valuative.LocalExtensionFinitePresentation`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Local finite presentation of the target over the base allows a compatible local ring homomorphism to extend to a morphism on a neighbourhood of the source point, for an arbitrary source scheme.

`AlgebraicGeometry.exists_open_morphism_inducing_localHom_of_locallyOfFinitePresentation` takes `X ⟶ S` and `Y ⟶ S`, points `x` and `y` above the same point `s` of `S`, and a local homomorphism from the stalk of `Y` at `y` to the stalk of `X` at `x`, compatible with the maps from the stalk of `S` at `s`. If `Y ⟶ S` is locally of finite presentation, the theorem gives an open neighbourhood `U` of `x` and an `S`-morphism `U ⟶ Y` carrying `x` to `y`. The induced stalk homomorphism is the prescribed one after transport along the equality of points and the canonical isomorphism for the open subscheme.

The proof chooses affine neighbourhoods of `s` and `y`, with the latter mapping inside the former. Over the affine base, the target section ring is finitely presented, and its map to the source stalk descends to a section ring on some neighbourhood by the filtered-colimit description of the stalk. Shrinking to an affine open gives a morphism by taking spectra. The remaining lemmas transport this morphism back to an open of `X` and recover the point and stalk equations from the factorization of the map from the spectrum of the source stalk through that open.

This is the local extension assertion of Tag 0BX6 under the local finite presentation hypothesis. The proof uses that hypothesis to descend the section-ring map and works with no germ injectivity assumption on `X`. The other reference is EGA I 6.5.1 (ii).

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [0BX6](https://stacks.math.columbia.edu/tag/0BX6) | `exists_open_morphism_inducing_localHom_of_locallyOfFinitePresentation` | local_extension |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | I 6.5.1 | `exists_open_morphism_inducing_localHom_of_locallyOfFinitePresentation` | (ii) |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Morphisms/Valuative/LocalExtensionFinitePresentation.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- One reference to EGA or SGA, written in the source as an attribute of that library, is taken out of the Lean text and listed above.
