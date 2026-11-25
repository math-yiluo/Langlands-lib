# Stalks of the pushforward under normalization

Module `StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Stalk`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For a scheme X whose quasi-compact opens each have finitely many irreducible components, the pushforward of the structure sheaf under normalization has two integral-closure descriptions at every point x.

## Stalk and ambient algebras

`normalizationPushforwardStalk` is the stalk at x of the pushforward. Its algebra structure over the local ring A = 𝒪ₓ, supplied by `normalizationPushforwardStalkAlgebra`, comes from the stalk of the normalization's structure-sheaf map.

- `normalizationPushforwardStalkEquivIntegralClosureReductionFractionRing` identifies this stalk as an A-algebra with the integral closure of A in the total fraction ring of A modulo its nilradical.
- `finite_minimalPrimes_stalk` shows that A has finitely many minimal primes. For any ring with that finiteness property, `minimalPrimes.reductionFractionRingAlgEquivResidueFieldProduct` identifies the total fraction ring of its reduction with the product of its minimal-prime residue fields, using the canonical map `minimalPrimes.residueFieldProductHom` on the product side.
- `normalizationPushforwardStalkEquivIntegralClosureMinimalPrimeResidueFields` transports the first integral-closure description along this product equivalence.

## Localization

`pushforwardStalk_isLocalization` applies to a quasi-compact, quasi-separated morphism f : Y ⟶ X and an affine neighborhood U of x. The stalk of the pushforward is the localization of the sections over f⁻¹(U) at the image of the complement of the prime for x in Γ(X, U). The proof uses the basic-open neighborhood basis and localization of sections over quasi-compact, quasi-separated schemes.

The normalization computation starts from the affine integral-closure description and uses `integralClosureLocalizationEquiv` to pass to the stalk. `fractionRingReductionLocalizationEquiv` identifies the localized ambient algebra, using `isFractionRing_localization_of_artinian`. These fraction-ring comparisons require an Artinian total fraction ring in the input, supplied here by the finite product of fields.

Both identifications concern the pushforward stalk at x. The algebra equivalences record compatibility with the local-ring map into that stalk.

Stacks Project, Tag 0C3B.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [0C3B](https://stacks.math.columbia.edu/tag/0C3B) | `normalizationPushforwardStalkEquivIntegralClosureReductionFractionRing` | the total ring of fractions of the reduction |
| [0C3B](https://stacks.math.columbia.edu/tag/0C3B) | `normalizationPushforwardStalkEquivIntegralClosureMinimalPrimeResidueFields` | the product of the minimal-prime residue fields |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Morphisms/Normalization/Stalk.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
