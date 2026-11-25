# Normalization over the spectrum of a local ring

Module `StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.LocalPullback`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Pulling the normalization of a scheme back to the spectrum of one of its local rings gives an affine scheme described by integral closure in a product of residue fields.

- `Scheme.exists_iso_pullback_fromSpecStalk` takes an affine, quasi-separated morphism f : Y ⟶ X and x in X. Its pullback over Spec 𝒪ₓ is isomorphic to the spectrum of the stalk of the pushforward of the structure sheaf of Y at x. The projection corresponds to the spectrum map of the canonical map from 𝒪ₓ to that stalk.
- `Scheme.exists_iso_pullback_normalization_fromSpecStalk` takes X, a point x and `hX`, the finiteness of irreducible components on all quasi-compact opens of X. Write A for the local ring at x and B for the integral closure of A in the product of the residue fields of its minimal primes, using the natural map from A to this product. The pullback of the normalization is isomorphic to Spec B over Spec A.

On an affine neighborhood of x the local ring and the pushforward stalk are corresponding localizations of the two section rings. The algebra pushout property of localization gives the first isomorphism. For the second, the stalk computation `normalizationPushforwardStalkEquivIntegralClosureMinimalPrimeResidueFields` identifies the pushforward stalk with B as an A-algebra.

References are Stacks Project Tag 0C3B and Tag 035N.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Morphisms/Normalization/LocalPullback.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
