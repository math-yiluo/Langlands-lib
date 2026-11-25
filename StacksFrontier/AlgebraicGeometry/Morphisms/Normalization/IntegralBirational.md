# Normalization through integral birational morphisms

Module `StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.IntegralBirational`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

An integral birational morphism α : X′ ⟶ X induces an isomorphism of the normalizations when the required finiteness of irreducible components holds. In particular the normalization map of X factors through α.

- `exists_normalizationFactorization_of_isIntegralHom_of_isBirational` assumes α integral, `hbirational : IsBirational α`, and `hX` and `hcomponents`. These last two require finitely many irreducible components on every quasi-compact open of X and on the inverse image of each such open under α, respectively. It gives the finiteness condition `hX'` on quasi-compact opens of X′, a factorization through X′, and an isomorphism to the normalization of X′ compatible with that factorization.
- `exists_normalizationFactorization_of_integral_of_birational` has the same conclusion when `hbirational` supplies birationality of the restriction over each quasi-compact open of X.

The local version first checks the generic-point bijection and the isomorphisms on generic local rings on quasi-compact neighborhoods to obtain global birationality. Each quasi-compact open upstairs is an open of the preimage of a finite union of affine opens downstairs and inherits finiteness of components from that preimage. The bijection on generic points and isomorphisms of residue fields identify the two coproducts of generic-point residue spectra. The universal property of relative normalization then gives the factorization and the comparison isomorphism.

Reference is the integral birational clause of Stacks Project Tag 035Q.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [035Q](https://stacks.math.columbia.edu/tag/035Q) | `exists_normalizationFactorization_of_integral_of_birational` | normalization_integral_birational |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Morphisms/Normalization/IntegralBirational.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
