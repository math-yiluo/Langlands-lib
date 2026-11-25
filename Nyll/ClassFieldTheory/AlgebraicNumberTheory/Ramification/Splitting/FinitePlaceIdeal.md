# Complete splitting of finite places via prime ideals

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Ramification.Splitting.FinitePlaceIdeal`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a finite Galois extension `L/K` of number fields, the library defines complete splitting of a finite place `v` of `K` by triviality of the decomposition group of one chosen extension of the `v`-adic absolute value. This file compares that definition with prime ideals: the decomposition group of any extension is the stabilizer of its centre prime, so complete splitting can be tested at any prime of `𝓞 L` above `v`. It also proves finiteness of the fibres of contraction and the passage to intermediate fields.

## Main results

- `absoluteValueDecompositionGroup_eq_finitePlaceStabilizer`: for any extension `w` of the `v`-adic absolute value to `L`, its decomposition group equals the stabilizer, under the Galois action on height-one primes of `𝓞 L`, of its centre prime `finitePlaceExtensionCentre v w`.
- `finitePlaceSplitsCompletely_iff_centre_stabilizer_eq_bot`: `v` splits completely iff that stabilizer is trivial, for any such `w`.
- `finitePlaceSplitsCompletely_iff_stabilizer_eq_bot`: `v` splits completely iff the stabilizer of a given prime `W` of `𝓞 L` lying above `v` is trivial.
- `finite_finitePlaceBelow_fibre`: only finitely many primes of `𝓞 L` lie above `v`; `Set.Finite.preimage_finitePlaceBelow` gives that the preimage of a finite set of places is finite. Neither needs `L/K` Galois.
- For an intermediate number field `M` with `L/M` Galois:
  - `finitePlaceEquiv_restrictAutomorphismScalars`: an `M`-automorphism acts on primes of `𝓞 L` in the same way when viewed as a `K`-automorphism;
  - `finitePlaceSplitsCompletely_over_intermediate_of_below`: if the place of `K` below a finite place `v'` of `M` splits completely in `L/K`, then `v'` splits completely in `L/M`;
  - `finite_nonsplittingPlaces_over_intermediate`: if only finitely many finite places of `K` fail to split completely in `L`, the same holds for `M`.

## Proof

The stabilizer comparison uses imported facts on how the centre prime transforms under conjugation of the extension and its injectivity. Independence from the extension rests on an imported result that triviality of the decomposition group does not depend on the extension chosen. Fibre finiteness uses Mathlib's finiteness of primes over a prime in a quasi-finite algebra. The intermediate-field statement compares stabilizers of a single prime of `𝓞 L` over `M` and over `K`.

## Points to watch

- "Splits completely" is the library's definition, triviality of a decomposition group; the count of primes above `v` does not appear.
- In the intermediate-field part, `L/M` Galois is an explicit instance hypothesis.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Ramification/Splitting/FinitePlaceIdeal.lean`: the Lean file is the source byte for byte (SHA-256 `0f6a7986fffb1f0908f9d3a33983ca4efdc19ca0027c81cbf04b49cc1e584b0c`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
