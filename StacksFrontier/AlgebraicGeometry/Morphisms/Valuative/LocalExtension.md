# Extending a homomorphism of local rings

Module `StacksFrontier.AlgebraicGeometry.Morphisms.Valuative.LocalExtension`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

A homomorphism from a target stalk to a source stalk can come from an actual morphism defined near the source point. This file proves existence for a target locally of finite type over the base when the source has an injective germ map at the chosen point.

In `AlgebraicGeometry.exists_open_morphism_inducing_localHom_of_isGermInjectiveAt`, the schemes `X` and `Y` are over `S` and the points `x ∈ X` and `y ∈ Y` lie over the same `s ∈ S`. The ring homomorphism from the stalk of `Y` at `y` to the stalk of `X` at `x` must be local and compatible with the two maps from the stalk of `S` at `s`. If `Y ⟶ S` is locally of finite type and `X.IsGermInjectiveAt x` holds, there is an open neighbourhood `U` of `x` and an `S`-morphism `U ⟶ Y` carrying `x` to `y` and inducing the given homomorphism. The equality uses the canonical stalk isomorphism for the open subscheme and transport along the equality of image points.

The variant `exists_open_morphism_inducing_localHom_of_isReduced` obtains germ injectivity for a reduced source with finitely many irreducible components, by `Scheme.isGermInjective_of_isReduced_of_finite_irreducibleComponents`. The module docstring also names variants for an integral and for a locally Noetherian source; they are not in this file.

The proof invokes Mathlib’s `spread_out_of_isGermInjective` to factor the map from the spectrum of the source stalk through `U`. The lemma `finish_local_extension_of_spec_eq` reads the image point and the map on local rings from this factorization by using the closed point of the local spectrum. Other helpers handle the base compatibility and transport of stalks.

The reduced variant gives a finite-type local extension case of Tag 0BX6 and is also referenced to EGA I 6.5.1 (ii).

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [0BX6](https://stacks.math.columbia.edu/tag/0BX6) | `exists_open_morphism_inducing_localHom_of_isReduced` | local_extension |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | I 6.5.1 | `exists_open_morphism_inducing_localHom_of_isReduced` | (ii), X reduced case |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Morphisms/Valuative/LocalExtension.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 11 declarations of the source file 9 are kept. The 2 left out are not needed by the results for which the extract is made: `AlgebraicGeometry.exists_open_morphism_inducing_localHom_of_isIntegral`, `AlgebraicGeometry.exists_open_morphism_inducing_localHom_of_isLocallyNoetherian`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- One reference to EGA or SGA, written in the source as an attribute of that library, is taken out of the Lean text and listed above.
