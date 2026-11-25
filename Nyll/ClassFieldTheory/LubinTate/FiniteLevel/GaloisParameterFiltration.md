# Principal-unit filtration on finite Lubin–Tate Galois groups

Module `Nyll.ClassFieldTheory.LubinTate.FiniteLevel.GaloisParameterFiltration`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `F` be a local field structure on `K` with residue field of cardinality `q`, and `π` a uniformizer. The injective homomorphism from the finite parameter group `O_Fˣ / U_F^(n+1)` to the Galois group of the standard level-`n` Lubin–Tate extension `L_n/K` carries the image of `U_F^k` to a subgroup of `Gal(L_n/K)`.

- `standardLubinTateGaloisParameterSubgroup F hπ n k`: that image subgroup.
- `standardLubinTateUnitParameterToGal_mem_galoisParameterSubgroup_iff`: a parameter maps into it iff it lies in the image of `U_F^k`; for `k ≤ n + 1`, the automorphism given by a unit `u` lies in it iff `u ∈ U_F^k`.
- `standardLubinTateUnitParameterSubgroupEquivGaloisParameterSubgroup`: the restricted map is a group isomorphism onto it.
- `standardLubinTateGaloisParameterSubgroup_natCard`: for `1 ≤ k ≤ n + 1`, it has `q^(n+1−k)` elements.

All of this follows from the injectivity of the parameter-to-Galois map and the count for the parameter filtration.

The subgroup is defined as an image of the unit filtration; it is not identified here with a ramification subgroup of `Gal(L_n/K)`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LubinTate/FiniteLevel/GaloisParameterFiltration.lean`: the Lean file is the source byte for byte (SHA-256 `fa9b081597d3740579e931444167225d6a74e0d6cac2d59dbc348f87fa042309`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
