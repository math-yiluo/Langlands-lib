# Decomposition groups and complete splitting at finite places

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Ramification.Splitting.FinitePlace`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a finite Galois extension `L/K` with `K` a number field, this file attaches to every finite place `v` of `K` a decomposition subgroup of `Gal(L/K)`, defines complete splitting of `v` by its triviality, and shows that the order of the decomposition group is the local degree.

## Main definitions and results

- `finitePlaceDecompositionGroup v`: the stabilizer in `L ≃ₐ[K] L` of `chosenFinitePlaceExtension v`, a chosen extension to `L` of the `v`-adic absolute value of `K`, constructed in another file. `mem_finitePlaceDecompositionGroup_iff` states membership as fixing that extension under conjugation.
- `FinitePlaceSplitsCompletely v`: this decomposition group is trivial.
- `finitePlaceLocalDegree v`: the dimension over the completion `K_v` of `LocalizedCompletion`, the library's algebraic localization of `L` at the chosen extension.
- `finitePlaceDecompositionGroup_card_eq_localDegree`: the order of the decomposition group equals the local degree.
- Characterizations: `v` splits completely iff the decomposition group has one element, iff the local degree is `1`; it does not split completely iff some `σ ≠ 1` fixes the chosen extension, iff the order exceeds `1`, iff the local degree exceeds `1`.
- `finitePlace_not_splitsCompletely_of_decompositionGroup_eq_top`: if `[L : K] > 1` and the decomposition group is all of `Gal(L/K)`, then `v` does not split completely.
- `absoluteValueDecompositionGroup_eq_bot_over_intermediate`: for an absolute value on `L` and an intermediate field `M`, triviality of its decomposition group over `K` implies triviality over `M`.
- `finitePlaceDecompositionGroupInQuotient v P`: the image of the decomposition group in `Gal(L/K)/P` for normal `P`; it is trivial iff the decomposition group lies in `P`.
- `finitePlace_exists_index_prime_quotient_of_decompositionGroup_ne_top`: if `Gal(L/K)` is cyclic of order `p^e` with `p` prime and `e > 0`, and the decomposition group is proper, there is a normal subgroup `P` of index `p` containing it, and the image in the quotient of order `p` is trivial.

## Proof

The order formula uses an imported isomorphism between the decomposition group and the automorphism group of the localization over `K_v`, imported results that this localization is finite and Galois over `K_v`, and `|Aut| = dimension` for Galois extensions.

## Points to watch

- Everything is defined from one chosen extension of the absolute value. The comment says the notion of complete splitting does not depend on the choice, by conjugacy, but the file does not prove this.
- Complete splitting is the library's definition, triviality of the decomposition group; its equivalence with the count of primes above `v` is not in this file.
- The comment calls the image in a quotient the decomposition group of the corresponding intermediate extension; the file only defines the image.
- `L` is not assumed to be a number field; only `[L : K]` finite and `L/K` Galois.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Ramification/Splitting/FinitePlace.lean`: the Lean file is the source byte for byte (SHA-256 `8eeb62916dd53b7e83e5912651453fdca6030be7a06befe014affd8f38653df2`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
