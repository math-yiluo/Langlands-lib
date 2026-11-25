# Galois-invariant units are the units of the base field

Module `Nyll.GaloisCohomology.Cyclic.TateH0.Invariants`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a finite Galois extension L/K, the units of L fixed by `Gal(L/K)` are exactly the units of K. The file states this for the unit representation `Rep.ofAlgebraAutOnUnits K L`, Mathlib's representation of the K-algebra automorphisms of L on `Additive Lˣ`.

## Main definitions and results

- `unitsInvariantSubmodule K L` is the ℤ-submodule of `Additive Lˣ` fixed by all automorphisms; it is defined for any field extension.
- `baseUnitToInvariantUnit` sends a unit of K to its image in L, which is invariant (any extension).
- `invariantUnitToBaseUnit` sends an invariant unit to a unit of K with the same image in L (`invariantUnitToBaseUnit_spec`); it needs L/K finite and Galois.
- The two maps are inverse to each other, and `invariantsUnitsAddEquivBaseUnits` and `invariantsUnitsEquivBaseUnits` package them as an additive and a ℤ-linear isomorphism `(Lˣ)^Gal(L/K) ≃ Kˣ` (written additively). `invariantsUnitsAddEquivBaseUnits_spec` says the image in L of the resulting unit of K is the original unit.

## Proof

An invariant unit is fixed by every element of the Galois group, so it lies in the image of K by Mathlib's `IsGalois.mem_range_algebraMap_iff_fixed`; the preimage is chosen with `Classical.choose`, and it is a unit because the original element is nonzero. Injectivity of `algebraMap K L` gives the inverse identities and additivity.

## Watch for

The unit group is written additively, as `Additive Lˣ` and `Additive Kˣ`, so that it is a ℤ-module.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/GaloisCohomology/Cyclic/TateH0/Invariants.lean`: the Lean file is the source byte for byte (SHA-256 `5f3513dede99184924167729d295d4a6799b65ff4dac7e5f0c28604c76a37f39`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
