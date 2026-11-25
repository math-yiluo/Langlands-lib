# Primes below P in the decomposition and inertia fields of number fields

Module `Nyll.ValuedFieldTheory.Ramification.HilbertRamification.Dedekind.PrimeContractions`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For number fields `K ⊆ L`, a group `G` acting on `L` over `K`, and an ideal `P` of `𝓞_L`, the file defines the primes below `P` in `𝓞_K` and in the rings of integers of the decomposition field `Z_P` and inertia field `T_P`, and sets up the instances needed to work in the tower `𝓞_K ⊆ 𝓞(Z_P) ⊆ 𝓞(T_P) ⊆ 𝓞_L`.

- `basePrime P`, `decompositionFieldPrime G P`, `inertiaFieldPrime G P`: `p = P ∩ 𝓞_K`, `P_Z = P ∩ 𝓞(Z_P)`, `P_T = P ∩ 𝓞(T_P)`. Instances say they are prime when `P` is, and that `P` lies over each of them, `P_T` over `P_Z` and `p`, and `P_Z` over `p`.
- `basePrime_ne_bot`, `decompositionFieldPrime_ne_bot`, `inertiaFieldPrime_ne_bot`: for `P` maximal, these contractions are nonzero (via `ringOfIntegers_under_ne_bot`).
- `ringOfIntegers_moduleFinite`: `𝓞_L` is a finite `𝓞_K`-module, recorded as a theorem because Mathlib does not find it by instance search.
- `inertiaField_algebra_decompositionField`, `ringOfIntegers_isScalarTower_decomposition_inertia`: `T_P` as a `Z_P`-algebra and the scalar tower on rings of integers.

No Galois hypothesis is used in this file.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Ramification/HilbertRamification/Dedekind/PrimeContractions.lean`: the Lean file is the source byte for byte (SHA-256 `4817c545588118b11b5d59511a5c036e3994d2a7c1ee3c142959e2389dc0623b`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
