# Finite places above v and exact extensions of the v-adic absolute value

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Completion.ExtensionIndex`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a finite extension L/K of number fields, this file matches the finite places of L above a finite place v of K with the absolute values on L that extend the normalized v-adic absolute value of K exactly. It prepares the comparison of the relative adelic tensor product with the adeles of L, and does not use restricted products.

## Definitions

- `finitePlaceBelow W`: the contraction W ∩ 𝓞 K of a height-one prime W of 𝓞 L. Simp lemmas: it is the identity when L = K, and transitive in a tower K ⊆ M ⊆ L.
- For `w : AbsoluteValueExtension (HeightOneSpectrum.adicAbv K v) L`:
  - `finitePlaceExtensionValuationSubring v w`: the valuation subring {x : w x ≤ 1} of L;
  - `finitePlaceExtensionCentreIdeal v w`: the prime of integers x of L with w x < 1 (`mem_finitePlaceExtensionCentreIdeal_iff`); `finitePlaceExtensionCentre v w` is the same ideal as a height-one prime.
- `finitePlaceExtensionEquivAbove v`: the bijection from such extensions w to the finite places W of L with `finitePlaceBelow W = v`, sending w to its centre.

## Main results

- `finitePlaceExtensionCentreIdeal_under`, `finitePlaceExtensionCentre_liesOver`: the centre lies over v.
- `finitePlaceExtensionValuationSubring_eq_localization`: the valuation subring of w is the localization of 𝓞 L at the centre.
- `finitePlaceExtensions_isEquiv_of_centres_eq`: exact extensions of finite places of two possibly different number fields F, M below L are equivalent absolute values on L when their centres agree.
- `finitePlaceExtensionCentre_injective`: an exact extension is determined by its centre.
- `finitePlaceExtensionCentre_conjugate`: for σ ∈ Aut(L/K), the conjugated extension has as centre the image of the old centre under `finitePlaceEquiv K L σ⁻¹`.
- `finitePlaceExtensionCentreInFibre_surjective`: every finite place of L above v is the centre of an exact extension.

## Proofs

The localization at the centre lies inside the valuation subring, which is not all of L because the v-adic absolute value is nontrivial; this forces equality. Injectivity: equal centres give equal valuation subrings, hence equivalent absolute values, and equivalent exact extensions of one absolute value are equal. Surjectivity is first shown for L/K Galois, using the transitive action of the Galois group on the primes over v. The general case passes to the finite normal closure M of L/K, lifts W to 𝓞 M, and restricts an extension on M to L.

## Points to watch

- `AbsoluteValueExtension` is the library's notion of an exact extension: the restriction to K equals `adicAbv K v` itself, not just an equivalent absolute value. The bijection is with these normalized extensions, not with places up to equivalence.
- Finite places are `HeightOneSpectrum` primes of the rings of integers, not Mathlib's `FinitePlace`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Completion/ExtensionIndex.lean`: the Lean file is the source byte for byte (SHA-256 `d5369c49db35073983e7e4ebeb8d0c83d48f9f557d4f042325e7c4949fc34261`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
