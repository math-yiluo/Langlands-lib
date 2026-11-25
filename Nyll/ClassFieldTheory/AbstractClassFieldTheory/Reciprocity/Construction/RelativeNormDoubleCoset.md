# Double-coset decomposition of a relative norm

Module `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.RelativeNormDoubleCoset`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a finite extension `S/K` of abstract fields (closed subgroups `G(S) ≤ G(K)` with `G(K)/G(S)` finite), the norm `N(S/K) : A_S → A_K` of a `G`-module `A` is the sum of the translates of an element over the cosets `G(K)/G(S)`. This file regroups that sum along the orbits of a subgroup `M` of `G(K)`, typically the group `G(K')` of an intermediate field, acting by left multiplication. The orbits are the double cosets `G(K') \ G(K) / G(S)`, and the elements of each orbit are indexed by cosets of a stabilizer. This is the norm side of the compatibility of reciprocity with the transfer.

## Main definitions and results

- `mem_relativeNormDoubleCoset_stabilizer_iff`: `k' ∈ G(K')` stabilizes the coset `t G(S)` if and only if `t⁻¹k't ∈ G(S)`.
- `relativeNormDoubleCosetEquiv`: Mathlib's class-formula bijection between `G(K)/G(S)` and pairs (an orbit `q`, a coset of the stabilizer of the representative of `q`). By `relativeNormDoubleCosetEquiv_symm_apply`, the inverse sends `(q, r)` to `r·(representative of q)`.
- `chosenOrbitClassEquiv_symm_apply`: the same description for any choice `φ` of orbit representatives, for a general group action.
- `relativeNorm_eq_sum_chosenOrbit_of_fintype`: `N(S/K)(a)` as a double sum, first over the orbits and then over the stabilizer cosets, with representatives `φ`, and finite enumerations (`Fintype` instances) of the orbit set and of the stabilizer coset spaces, supplied by the caller.
- `relativeNorm_eq_sum_doubleCoset_of_fintype`, `relativeNorm_eq_sum_doubleCoset`: the same with the standard representatives, for caller-supplied or built-in finite enumerations (`relativeNormDoubleCosetOrbitFintype`, `relativeNormDoubleCosetStabilizerFintype`).

## Watch for

The equalities hold in the underlying module `A`, after coercion out of `A_K`. They are additive, since the module is written additively. Representatives are fixed choices (`Quotient.out` or the supplied `φ`), but the sums do not depend on them.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/RelativeNormDoubleCoset.lean`: the Lean file is the source byte for byte (SHA-256 `7c0644ac0a25241ee7f9dd97a67246874525fbca1ce769a892c5805f63d1f7ee`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
