# The affine description of normalization

Module `StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Affine`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Over an affine open of a reduced scheme, normalization is the spectrum of the integral closure of the coordinate ring in its total ring of fractions. The file also gives the affine description of relative normalization.

- `preimageNormalizationIsoSpecIntegralClosure` constructs the isomorphism over an open U presented by a chosen isomorphism Spec A ≅ U. Its hypothesis `hX` requires finitely many irreducible components on every quasi-compact open of the reduced scheme X. `preimageNormalizationIsoSpecIntegralClosure_hom_comp` identifies the restricted normalization map with the spectrum map of A into that integral closure.
- `relativeNormalizationPreimageIso` takes a quasi-compact, quasi-separated morphism f : Y ⟶ X. Over an affine open U of X it identifies the relative normalization with the spectrum of the integral closure of Γ(X, U) in Γ(Y, f⁻¹(U)). `relativeNormalizationPreimageIso_comp` identifies the map down to U.
- `genericPreimageIsoSigma` identifies the inverse image of an open under the generic-point residue spectrum map with the coproduct of the residue-field spectra at the generic points in that open. When U contains finitely many generic points, `genericPreimageSectionsRingEquiv` identifies the section ring on its preimage with the product of their residue fields. On a reduced affine chart, `genericPreimageSectionsAlgEquivFractionRing` identifies this product with the total ring of fractions as an algebra over the chart ring.

The proof pairs generic points with minimal primes and uses reducedness to identify their residue fields with the prime localizations. The product of these localizations gives the total ring of fractions. The affine normalization follows by transporting integral closure through that identification and the chosen coordinate-ring isomorphism.

References are Stacks Project Tag 035P, EGA I 1.1.14 for components and minimal primes, and SGA 3 VIB 3.11 (partial) for the residue map at a generic point.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [035P](https://stacks.math.columbia.edu/tag/035P) | `preimageNormalizationIsoSpecIntegralClosure_hom_comp` | affine_normalization |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | I 1.1.14 | `componentsEquivMinimalPrimes` |  |
| SGA | 3 VIB 3.11 | `residue_isIso_of_genericPoint` | partial |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Morphisms/Normalization/Affine.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 2 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
