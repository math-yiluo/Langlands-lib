# Prime Artin elements on subfields of ray class fields

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.RayClassSubgroupPrimeArtin`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a modulus `m` of a number field `K` and a subgroup `H` of the ray class group, the library defines the subfield of the ray class field fixed by `H`, viewed as a finite abelian extension `rayClassSubgroupSubextension m H` inside the separable closure of `K`, with an Artin map `rayClassSubgroupArtin m H` from the ray class group onto its automorphisms. The file shows that this Artin map is the arithmetic prime Artin element on the ray class of a prime idèle.

## Main result

- `rayClassSubgroupArtin_finitePrimeIdele`: for every finite prime `v` of `K`, `rayClassSubgroupArtin m H` sends the ray class of the prime idèle `finitePrimeIdele v` to `arithmeticFinitePlacePrimeArtin v` of the extension `rayClassSubgroupSubextension m H`.

## Proof

Three private lemmas carry the argument.

- In the full ray class field, the inverse reciprocity isomorphism sends the inverse of the ray class of the prime idèle to the arithmetic prime Artin element. This holds because the reciprocity isomorphism is geometrically normalized and inverts the arithmetic global norm-residue symbol.
- Restricting an automorphism of the ray class field to the fixed field agrees with restricting it to the embedded copy in the separable closure.
- For abelian `L ⊇ E ⊇ K`, restriction from `L` to `E` sends the arithmetic prime Artin element of `L` to that of `E`, a consequence of the compatibility of the global Artin map with towers.

## Points to watch

- The statement has no hypothesis on `v`: it covers primes dividing `m` as well, because it is phrased with the prime idèle rather than with an ideal prime to `m`.
- The right-hand side is the library's arithmetic prime Artin element, not Mathlib's Frobenius.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/GlobalClassFields/RayClassSubgroupPrimeArtin.lean`: the Lean file is the source byte for byte (SHA-256 `5858e4f6aed3d155019fc3ccb65421a6388b5ed2e9dc75a8c0cebd92b4455ff7`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
