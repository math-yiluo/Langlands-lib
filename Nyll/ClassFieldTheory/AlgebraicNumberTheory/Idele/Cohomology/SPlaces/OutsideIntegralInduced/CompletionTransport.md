# Transporting completions along right cosets of a decomposition group

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.OutsideIntegralInduced.CompletionTransport`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `L/K` be a finite Galois extension of number fields, `vK` a nontrivial absolute value on `K` and `w` an extension of `vK` to `L`, with decomposition group `D_w`. Each right coset `q` of `D_w` gives an extension of `vK` to `L` (`rightCosetExtensionEquiv`), the conjugate of `w` by a representative `Quotient.out q`. The file transports the completion at that extension to the library's local field `LocalizedCompletion vK w` attached to `w`.

- `rightCosetCompletionRingEquivLocalized vK hvK w q`: a ring isomorphism from the completion at the conjugate extension to `LocalizedCompletion vK w`, Galois conjugation followed by the inverse of `localizedCompletionEquivCompletion`.
- `rightCosetCompletionRingEquivLocalized_norm_eq`: this isomorphism preserves norms.
- `rightCosetCompletionIntegersRingEquivLocalized`: when `vK` is nonarchimedean, its restriction to an isomorphism of the valuation rings, obtained from the norm equality and the description of both rings as the elements of norm at most one.

The isomorphisms depend on the chosen coset representative `Quotient.out q`. `K` and `L` are taken in `Type`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Idele/Cohomology/SPlaces/OutsideIntegralInduced/CompletionTransport.lean`: the Lean file is the source byte for byte (SHA-256 `d27c2dd745853a2b6c6eb7f71b4d97512656470eb35b2016ae89cd23d30c3cf2`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
