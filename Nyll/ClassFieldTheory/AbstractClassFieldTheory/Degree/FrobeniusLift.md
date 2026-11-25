# Frobenius lifts of finite Galois automorphisms

Module `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusLift`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `K` be an abstract field of finite residue degree (a closed subgroup `G_K` of `G` with degree datum `d`) and `L` a closed subgroup of `G_K` that is normal in it, so that `L | K` is Galois. The file forms the group `G(L̃|K)` as the quotient `G_K / (G_L ∩ I_K)`, its normalized degree map to `ℤ̂`, the restriction to `G(L|K) = G_K / G_L`, and the Frobenius elements: classes whose normalized degree is a positive natural number. It proves that for finite `L | K` every element of `G(L|K)` comes from a Frobenius element.

## Main definitions and results

- `exists_positive_nsmul_one_sub_mem_of_index_ne_zero`: if an additive subgroup `H` of `ℤ̂` has nonzero index, every `z ∈ ℤ̂` is congruent modulo `H` to `n · 1` for some `n > 0`.
- `extensionInertiaWithin`: `G_L ∩ I_K` inside `G_K`, standing for the subgroup fixing `L̃`; it is normal when `G_L` is normal in `G_K`.
- `extensionNormalizedDegree`: the normalized degree `d_K` factored through `G_K / (G_L ∩ I_K)`.
- `extensionRestriction`: the projection `G_K / (G_L ∩ I_K) → G_K / G_L`.
- `FrobeniusElements`: the classes `σ` with `d_K(σ) = n · 1` for some `n > 0`; `frobeniusRestriction` is restriction on them.
- `frobeniusRestriction_surjective`: if `G_L` is normal and of finite index in `G_K`, restriction maps the Frobenius elements onto `G_K / G_L`.

The proof shows that `d_K(G_L)` has finite index in `ℤ̂` (using surjectivity of `d_K`), picks `n > 0` with `d_K(s) ≡ n` modulo it, and corrects `s` by an element of `G_L`.

## Points to watch

- Positivity of `n` is explicit, since Lean's `ℕ` contains `0`.
- `FrobeniusElements` is a subtype; although called a semigroup, no multiplication on it is defined in this file.
- `L̃` is never constructed as a field: `G(L̃|K)` is only the quotient group above.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/FrobeniusLift.lean`: the Lean file is the source byte for byte (SHA-256 `8cd93e3572b24ac858a11f6fd1c6f6410f10ef88578aea5040ebdbcce3eab82c`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
