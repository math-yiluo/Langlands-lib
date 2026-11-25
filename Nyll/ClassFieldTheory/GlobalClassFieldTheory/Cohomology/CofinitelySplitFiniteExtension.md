# Extensions in which almost all places split are trivial

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.Cohomology.CofinitelySplitFiniteExtension`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a finite extension of number fields `L / K`, if all but finitely many finite places of `K` split completely in `L`, then `L = K`.

- `finrank_eq_one_of_finite_nonSplittingPlaces`: if the set of finite places `v` of `K` that do not split completely in `L` (`FinitePlaceSplitsCompletelyInExtension`) is finite, then `[L : K] = 1`.
- `algEquivBaseOfFiniteNonSplittingPlaces`: the same conclusion as a `K`-algebra isomorphism `L ≃ₐ[K] K`.

The proof passes to the normal closure `M` of `L / K`, to which the finiteness transfers. If `M ≠ K`, an automorphism of prime order `p` gives an intermediate field `K'` with `M / K'` cyclic of degree `p`. An imported result gives infinitely many places of `K'` whose decomposition group in `M / K'` is the whole group; such places do not split completely, contradicting the finiteness transported to `K'`.

`L` need not be Galois over `K`; only finite places are considered; `K` and `L` live in `Type`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/Cohomology/CofinitelySplitFiniteExtension.lean`: the Lean file is the source byte for byte (SHA-256 `23800e84a0a1644e52837da2023d38fa529cde78019779bb6aaaa6ba1ba5b9dc`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
