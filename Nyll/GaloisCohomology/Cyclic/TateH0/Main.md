# Degree-zero Tate cohomology of Lˣ is the norm quotient

Module `Nyll.GaloisCohomology.Cyclic.TateH0.Main`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a finite Galois extension L/K, the degree 0 Tate group of `Gal(L/K)` acting on `Lˣ` is `Kˣ` modulo the norms from `Lˣ`, the library's `NormQuotient K L`. The file gives this identification for the three versions of integral Tate cohomology in the library.

- `invariantsQuotientAddEquivNormQuotient`: the invariant units modulo the image of the representation norm are isomorphic to `NormQuotient K L`, a class going to the norm class of the corresponding unit of K.
- `integralH0TateUnitsAddEquivNormQuotient` and `universeH0TateUnitsAddEquivNormQuotient`: the same for `IntegralGroupCohomology.tate` and `IntegralGroupCohomology.Universe.tate` in degree 0, for fields in any universes.
- `H0TateUnitsIsoNormQuotient`: for K and L in `Type`, an isomorphism of ℤ-modules from Mathlib's `tateCohomology (Rep.ofAlgebraAutOnUnits K L) 0`, compatible with the integral version (`H0TateUnitsIsoNormQuotient_integral`).
- `integralH0TateUnitsAddEquivNormQuotient_connecting`: for a short exact sequence `Lˣ → B → C`, the connecting map from degree −1 agrees under these identifications with Mathlib's.

The comparison with Mathlib's Tate cohomology needs K and L in universe 0. Units are written additively, and the isomorphisms other than `H0TateUnitsIsoNormQuotient` are only additive (`≃+`).

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/GaloisCohomology/Cyclic/TateH0/Main.lean`: the Lean file is the source byte for byte (SHA-256 `7107a267041e7a63d6ef5ec5a5cb153c96a72e3c0670d6e8fe276db9f64efbd3`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
