# Root quotients and root characters in Kummer theory

Module `Nyll.GaloisCohomology.Kummer.Concrete.RootCharacters`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The file provides the basic algebra of the map `σ ↦ σ(β)/β` for a unit `β` of a field extension `L/K`, and of radical data, which choose an `n`-th root in `L` of each element of a subgroup of `Kˣ`. When Galois fixes the `n`-th roots of unity, the root quotients of the chosen roots of a radical datum become characters of `Gal(L/K)` with values in `μ_n(L)`.

## Main definitions

- `nthRootsSubgroup L n`: the subgroup `μ_n(L)` of units `u` with `u^n = 1`; Galois automorphisms preserve it (`smul_mem_nthRootsSubgroup`).
- `rootQuotient β σ`: the unit `σ(β)/β`.
- `RadicalDatum n`: a structure with a subgroup `carrier ≤ Kˣ`, a function `root` choosing for each `a` a unit of `L` with `root a ^ n = a`.
- `RadicalDatum.rootCocycle`: the root quotient of the chosen root.
- `RadicalDatum.rootCharacter a hfixed`: the same map as a homomorphism `Gal(L/K) →* Lˣ`, under the hypothesis `hfixed` that every automorphism fixes every `u` with `u^n = 1`.

## Main results

- `rootQuotient_mul`, `isMulCocycle₁_rootQuotient`: `σ ↦ σ(β)/β` is a multiplicative `1`-cocycle; also identities for products, quotients, inverses, base-field units (trivial quotient) and `rootQuotient_eq_one_iff` (trivial exactly when `σ` fixes `β`).
- `rootQuotient_map_restrictNormal`, `rootQuotient_map_algEquiv`: compatibility with restriction to a normal subextension and with transport along a `K`-algebra isomorphism.
- `rootQuotient_pow_eq_one_of_pow_fixed`, `rootQuotient_mem_nthRootsSubgroup_of_pow_fixed`: if `β^n` is Galois-fixed, the root quotients lie in `μ_n(L)`.
- `rootCocycle_mem_nthRootsSubgroup`, `changeRoot_rootQuotient_mem_nthRootsSubgroup`: root cocycles, and the change between two roots of the same element, take values in `μ_n(L)`.
- `rootQuotient_eq_rootCocycle_of_same_pow`, `rootCharacter_eq_of_same_pow`: under `hfixed`, any root of `a` gives the same root quotient as the chosen one.

## Points to watch

- `nthRootsSubgroup` is the library's subgroup of `Lˣ`, not Mathlib's `rootsOfUnity`.
- `hfixed` is an explicit hypothesis saying that every automorphism fixes `μ_n(L)` pointwise, as happens when `μ_n(L)` lies in the image of `K`; the character property and the independence of the root depend on it.
- A radical datum is extra data: the roots are chosen, and need not be multiplicative in `a`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/GaloisCohomology/Kummer/Concrete/RootCharacters.lean`: the Lean file is the source byte for byte (SHA-256 `55b91b9a1ace770ec92435e09a0c52f3f02c9749ace49718b3caabd8a20fae06`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
