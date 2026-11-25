# Places with full decomposition group in cyclic p-power extensions

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.Cohomology.CyclicPrimePowerFullDecomposition`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `L / K` be a cyclic Galois extension of number fields of degree `p^e`, `p` prime, `e > 0`. The file proves that infinitely many finite places of `K` have decomposition group all of `Gal(L/K)`, i.e. have a single place above them in `L`. Along the way it shows that if almost all places split completely in a finite Galois extension, the idele class norm is surjective.

## Main results

- `cyclicPrimeSubextensionDecompositionGroup_eq_bot_of_ne_top`: if the decomposition group of `v` in `L / K` is proper, its image in the chosen subextension `M` of degree `p` is trivial, since every proper subgroup of a cyclic `p`-group lies in the subgroup of index `p`.
- `finitePlaceSplitsCompletely_in_cyclicPrimeSubextension_of_decompositionGroup_ne_top`: such a place `v` splits completely in `M`.
- `ideleClassNorm_range_eq_top_of_splitsCompletely_outside`: for `E / K` finite Galois, if every finite place outside a finite set `S` splits completely in `E`, the idele class norm `C_E → C_K` is surjective; `ideleClassNorm_index_eq_one_of_splitsCompletely_outside` restates this as index one. The proof uses an imported approximation lemma: each idele class has a representative that is a local norm everywhere, hence a global idele norm.
- `cyclic_prime_power_fullDecompositionPlaces_infinite_of_primeSubextension_normIndex`: the infinitude, assuming `p ≤ [C_K : N C_M]`.
- `cyclic_prime_power_infinite_fullDecompositionPlaces`: the infinitude, unconditionally.
- `exists_fullDecompositionPlace_outside_finset` and its conditional variant: for every finite set `S` there is such a place outside `S`.

## Proof

If only finitely many places had full decomposition group, all others would split completely in `M`, so the norm index of `M / K` would be `1`, contradicting `p ≤ [C_K : N C_M]`. The unconditional version obtains that bound from the imported inequality `finrank_le_ideleClassNorm_index` for the cyclic extension `M / K`.

## Points to watch

- The conditional theorems carry the hypothesis `hLower : p ≤ [C_K : N C_M]`, which stands for the first inequality of class field theory for `M / K`.
- `M` is a chosen subextension (`cyclicPrimeSubextension`); "splits completely" means the decomposition group at a chosen extension of the place is trivial.
- Only finite places are considered; `K` and `L` live in `Type`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/Cohomology/CyclicPrimePowerFullDecomposition.lean`: the Lean file is the source byte for byte (SHA-256 `eebe83b2b9fdc75e05fb549906493feb4ec9d5d65db811e93746f626c1172ceb`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
