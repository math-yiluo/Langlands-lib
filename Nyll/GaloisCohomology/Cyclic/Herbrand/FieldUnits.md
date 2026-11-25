# Fixed units and the norm quotient

Module `Nyll.GaloisCohomology.Cyclic.Herbrand.FieldUnits`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a finite Galois extension L/K, this file identifies the degree-zero Herbrand group of the units Lˣ, the fixed units modulo norms, with the norm quotient Kˣ / N(Lˣ).

- `LocalClassFieldTheory.additiveFixedUnitsEquivInvariants`: the Gal(L/K)-fixed subgroup of Lˣ and the invariant submodule of the unit representation are the same additive group.
- `fixedUnitsEquivBaseUnits`: the fixed subgroup of Lˣ is isomorphic to Kˣ; `_spec` says the image of a fixed unit, embedded back into L, is the unit itself.
- `tateNorm_units_val`: the norm of the Herbrand theory, the product of the Galois conjugates of `a`, is the image in L of the field norm of `a` from L to K.
- `fixedUnitsEquivBaseUnits_map_normSubgroup`: under this isomorphism, the norm subgroup of the Herbrand theory goes exactly to the subgroup of field norms of units.
- `herbrandH0UnitsEquivNormQuotient`: hence `HerbrandH0 Gal(L/K) Lˣ` is isomorphic to `NormQuotient K L`; `_mk` says a fixed unit goes to the class of its value in Kˣ.

K and L may live in different universes.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/GaloisCohomology/Cyclic/Herbrand/FieldUnits.lean`: the Lean file is the source byte for byte (SHA-256 `7bc26d7b3eadeba2afdbaff0ea0350af8bb5789a34bd81b65f17f70b1fce1754`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
