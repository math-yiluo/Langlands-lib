# Fixed fields of elements of prime order and complete splitting

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Ramification.Splitting.PrimeOrderFixedField`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Given a finite Galois extension `L/K` of degree greater than one, this file picks an automorphism `σ` of prime order `p` and forms `K' = L^⟨σ⟩`, so that `L/K'` is cyclic of degree `p`. It also shows that complete splitting of a finite place passes from `L/K` to `L/K'` for places of `K'` above it. This prepares a reduction to the cyclic case of prime-power degree.

## Main definitions and results

- `exists_prime_order_automorphism_of_one_lt_finrank`: if `[L : K] > 1`, `Gal(L/K)` has an element of prime order (Cauchy's theorem in Mathlib).
- `fixedFieldPrime`, `primeOrderAutomorphism`, `primeOrderSubgroup`: a chosen prime `p`, an automorphism of order `p`, and the subgroup it generates, of order `p`.
- `primeOrderFixedField`: the fixed field `K'`. Instances make `L/K'` Galois with cyclic group; `primeOrderFixedField_finrank` and `primeOrderFixedField_card_aut` give `[L : K'] = |Gal(L/K')| = p`. `primeOrderFixedField_threeSeven_data` bundles primality of `p`, the Galois and cyclic properties of `L/K'`, and `|Gal(L/K')| = p`.
- `FinitePlaceLiesAbove v v'`: for number fields `K ⊆ M`, the normalized `v'`-adic absolute value of `M` restricts exactly to the normalized `v`-adic absolute value of `K`.
- `finitePlaceSplitsCompletely_over_intermediate_of_liesAbove`: for `K ⊆ M ⊆ L` with `L/K` and `L/M` Galois, if `v` splits completely in `L/K` and `v'` lies above `v` in this sense, then `v'` splits completely in `L/M`. `finitePlaceSplitsCompletely_over_primeOrderFixedField_of_liesAbove` specializes this to `M = K'`.

## Proof

The chosen extension of `v'` to `L` is also an extension of `v`, by the hypothesis. An imported result makes triviality of the decomposition group independent of the extension chosen, and a lemma from another file carries triviality from `K` to `M`.

## Points to watch

- `FinitePlaceLiesAbove` is the library's own relation. Both absolute values are normalized (Mathlib's `adicAbv` uses the norm of the prime), so exact restriction should hold only when `v'` has local degree one over `v`. It is therefore stronger than `v'` lying over `v`.
- `p`, `σ` and `K'` are fixed by choice, and `K'` depends on the element chosen; the results use only that `σ` has prime order `p`.
- "Splits completely" is the library's decomposition-group definition, taken at a chosen extension of the absolute value.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Ramification/Splitting/PrimeOrderFixedField.lean`: the Lean file is the source byte for byte (SHA-256 `71402a99fbfe7805c1816c515839ac4a4b369cae0ad5bd4797119642498faaaa`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
