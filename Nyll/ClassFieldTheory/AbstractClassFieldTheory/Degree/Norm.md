# The norm of a finite extension of abstract fields

Module `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Degree.Norm`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `A` be a `ℤ`-linear representation of the group `G`, and let abstract fields be closed subgroups of `G`, with `G_L ≤ G_K` of finite index. The file defines the norm `N(L/K) : A_L → A_K` from the elements fixed by `G_L` to those fixed by `G_K`, as the sum of `σ a` over the left cosets `σ G_L` of `G_K`. It is the additive form of the usual product over coset representatives, and it does not need `L | K` to be Galois.

## Main definitions and results

- `relativeCosetAction`: for `a` fixed by `G_L`, the value `σ a` at a left coset `σ G_L`, well defined because `a` is fixed by `G_L`; it is additive in `a` (`relativeCosetAction_add`, `relativeCosetAction_zero`).
- `leftMulCosetEquiv`: left multiplication by `g` as a permutation of the cosets `G / H`, for any subgroup `H`.
- `relativeNormValue`: the sum over all cosets, an element of the module `A`.
- `relativeNormValue_fixed`: this sum is fixed by `G_K`, since left multiplication by `k ∈ G_K` only permutes the cosets.
- `relativeNorm`: the norm as an additive homomorphism `A_L → A_K`; `relativeNorm_apply_coe` gives its value as the explicit sum.

## Points to watch

- Finiteness of `G_K / G_L` is an instance argument; no topological hypothesis is used, although `G` carries a topology and the fields are closed subgroups.
- The fixed submodules are the library's `ambientFixedAddSubgroup`, and `A` is a Mathlib `Rep ℤ G`; no continuity of the action is assumed.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Norm.lean`: the Lean file is the source byte for byte (SHA-256 `9dd27d05f64f04f7f54fadb9ebc768c9f0b93d1f0b56cd033c02034939b3b760`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
