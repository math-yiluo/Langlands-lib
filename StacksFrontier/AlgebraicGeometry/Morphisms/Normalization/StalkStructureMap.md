# Normalization stalks over an affine base

Module `StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.StalkStructureMap`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

When X is over Spec R, the local-ring description of its normalization can be made compatible with the structure map from R. The normalization requires that every quasi-compact open of X have finitely many irreducible components.

- `exists_ringEquiv_stalk_normalizationScheme_localizationAtPrime_germ` applies at a normalization point y over x. It identifies the local ring at y with a prime localization of the integral closure of 𝒪ₓ in the product of its minimal-prime residue fields. The isomorphism carries the germ of the R-structure map at y to the image of the germ at x.
- `exists_ringEquiv_stalk_normalizationScheme_localizationAtPrime_germ_of_isLocalization` assumes 𝒪ₓ is a localization of S, that the total fraction ring of the reduction of S is Artinian, and that the germ at x factors through ι : R → S via `hι`. The target is now a prime localization of the integral closure of S in that fraction ring, with the structure map induced by ι.
- `exists_ringEquiv_stalk_normalizationScheme_pullback_localizationAtPrime_germ` treats W = X ×₍Spec A₎ Spec B under the component-finiteness hypothesis on W. Here B is finite flat over A and its localization L at the image of the non-zero-divisors of A is finite over the total fraction ring K of A. Given an A-compatible identification of the local ring at the image of w with a domain O of Artinian fraction ring F, the result at a normalization point over w uses the integral closure of O in the reduction of F ⊗[K] L. The isomorphism respects the B-structure map via the right tensor factor of O ⊗[A] B.
- Two general lemmas transport localizations at primes. `exists_ringEquiv_localizationAtPrime_of_ringEquiv` does so along a ring isomorphism. By `exists_ringEquiv_localizationAtPrime_of_localizationAlgEquiv`, if a C-algebra D is isomorphic over C to the localization of an S-algebra E at the image of a submonoid of S, with compatible maps from S, then each localization of D at a prime is isomorphic to a localization of E at a prime, compatibly with the images of S.

For a commuting square over X whose corner P is identified with Spec T over Spec 𝒪ₓ, `germ_stalkMap_square` equates by naturality of germs the two maps from R to the local ring of P at a point w. The proof uses the affine description of the normalization after this pullback, then transports the prime localizations through the algebra equivalences from localization and tensor product.

The base change result gives the local-ring comparison with the base already specified. The base rings and schemes in these statements use a common universe.

Stacks Project, Tag 0C3B and Tag 09IL.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Morphisms/Normalization/StalkStructureMap.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
