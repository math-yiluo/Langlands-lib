# The narrow finite conductor of an idèle-class norm group

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.NormConductor`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a finite Galois extension `L/K` of number fields, the file constructs from the extension itself a modulus whose ray congruence subgroup lies in the idèle-class norm range `N(C_L)`. It deduces that `N(C_L)` is open, closed and of finite index, defines its narrow finite conductor, and shows that this conductor is supported only at ramified finite primes.

## Construction

- `exists_localHigherUnitGroup_le_chosenFinitePlaceLocalNormSubgroup`: at each finite place `v`, some higher unit group `U_v^(n)` lies in the local norm subgroup at a chosen place above `v`, because that subgroup is open.
- `ideleClassNormLocalHigherUnitExponent v`: the least such `n`, with `_spec` and `_min`. It is `0` exactly when all integral units are local norms (`_eq_zero_iff`), in particular when the chosen place is unramified or `v` is not a ramified prime.
- `ideleClassNormDefiningModulus`: the finite modulus `v ↦` that exponent. It is supported in the ramified primes and is pointwise least among moduli with the same local property (`ideleClassNormDefiningModulus_le_of_localHigherUnitGroup_le`). `mem_ideleClassNormDefiningModulus_support_iff` describes its support.
- `ideleClassNormDefiningModulus_isDefiningModulus`: its narrow version, with positivity at every real place, is a defining modulus for `N(C_L)`. Archimedean positive elements are local norms, and the prescribed higher units are local norms; the imported criterion `mem_relativeIdeleNorm_range_iff_localTensorNorms` assembles these into a global norm.

## Main results

- `ideleClassNormConductorialSubgroup`: `N(C_L)` as a `ConductorialSubgroup K`. `ideleClassNormNarrowFiniteConductor`: its narrow finite conductor, itself a defining modulus (`ideleClassNorm_narrowFiniteConductor_isDefiningModulus`).
- `ideleClassNorm_range_isOpen`, `ideleClassNorm_range_isClosed` and the instance `ideleClassNorm_rangeFiniteIndex`.
- `narrowFiniteConductorRayClassGroupToIdeleClassNormQuotient`: the surjection from the ray class group of the narrow conductor onto `C_K ⧸ N(C_L)`. Its kernel is the image of `N(C_L)`, which gives an isomorphism, a factorization of the ray class number and the divisibility of orders.
- The conductor is bounded by the constructed modulus pointwise and in support.
- A prime `v` is absent from the conductor if the unit class subgroup at `v` lies in `N(C_L)`, if the chosen prime above `v` is unramified, or if `v` splits completely. Hence `ideleClassNorm_narrowFiniteConductor_support_subset_ramifiedBaseFinitePlaces`.

## Points to watch

- Only the finite part of the conductor is defined, always paired with every real place (a narrow modulus); the module docstring says the full conductor with an archimedean component is deliberately not defined here.
- `L/K` is only assumed Galois, not abelian.
- Local conditions refer to a chosen place above `v`; the unramifiedness criterion asks only about the chosen prime.
- The conductor is shown to be at most the constructed modulus, not equal to it.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/GlobalClassFields/NormConductor.lean`: the Lean file is the source byte for byte (SHA-256 `db39bd57398249e48f750b55d062ff12a44060534f0b057ca2303b9138605954`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
