# The finite-place Artin map does not depend on the place above

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FinitePlaceArtin.Conjugation`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let L/K be a finite abelian extension, with K a number field, and v a finite place of K. The library defines a local Artin homomorphism at v from a chosen extension w of the v-adic absolute value to L. Its values are taken in the decomposition group of w inside Gal(L/K). This file shows that the result does not depend on w: conjugating w by g ∈ Gal(L/K) leaves the map unchanged, and any two extensions are conjugate.

## Main definitions and results

- `finitePlaceConjugateLocalizedCompletionAlgEquiv v w g`: an isomorphism over K_v from the localized completion at the conjugate place w^g (`absoluteValueExtensionConjugate`) to the localized completion at w. It is built from the conjugation isomorphism of completions. Two lemmas say that it sends the image of x ∈ L to the image of g x, and that its inverse sends x to g⁻¹ x.
- `finitePlaceDecompositionTransport_conjugate` (and its pointwise form `..._apply`): the identifications of the decomposition groups of w and w^g with the automorphism groups of their localized completions are compatible with that isomorphism, once included in Gal(L/K).
- `finitePlaceLocalArtinMonoidHom_conjugate`: the local Artin maps for w^g and w agree after transport along that isomorphism. This is the naturality `abelianLocalArtinMonoidHom_autCongr` of local reciprocity.
- `finitePlaceArtinMonoidHomOfExtension_conjugate`: the Artin homomorphism into Gal(L/K) built from w^g equals the one built from w.
- `finitePlaceArtinMonoidHomOfExtension_eq`: for any two extensions w, w' of the v-adic absolute value to L, the two Artin homomorphisms coincide.

## Proof

The decomposition-group comparison uses that Gal(L/K) is commutative, so g commutes with every decomposition element. For the last statement, the centres of w and w' are primes of 𝓞 L over v. Galois acts transitively on these (`exists_smul_eq_of_isGaloisGroup`), so w' is a conjugate of w, because an extension is determined by its centre (`finitePlaceExtensionCentre_injective`).

## Points to watch

- Abelianness of L/K is used in an essential way: commutativity in the decomposition-transport step. For non-abelian extensions the decomposition groups of conjugate places differ by conjugation.
- `NumberField L` is not assumed; it is derived from finiteness over K where needed.
- The local Artin maps are the library's own, taken from its local class field theory.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/Reciprocity/FinitePlaceArtin/Conjugation.lean`: the Lean file is the source byte for byte (SHA-256 `08d7927343158b5870dc17ca2a95aa328b0960f37c8467b866853ef9d518fb06`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
