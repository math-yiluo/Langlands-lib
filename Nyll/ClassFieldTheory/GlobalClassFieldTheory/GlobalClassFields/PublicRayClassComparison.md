# Ray class groups and ray class fields: public statements

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.PublicRayClassComparison`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The file proves the public statements on conductors and ray class fields. It relates the public, ideal-theoretic notions (`RayClassModulus`, `IsRayCongruent`, `RayClassGroup`) to the library's idelic ray class theory, transfers the properties of the selected ray class fields, and shows that the full conductor of the norm group is the abelian conductor in the public sense.

## Comparison of ray class groups

- `rayClassModulusToOriginal`: a public modulus read as a library modulus, with the same finite exponents and real places.
- `principalIdele_mem_primeTo_iff_isRayCongruent`: the principal idèle of `x` is prime to `m` in the library's sense exactly when `IsRayCongruent m x` (positive at the chosen real places, in the prescribed higher unit groups at the primes of `m`).
- `rayPrincipalIdealSubgroup_eq`: the public and library ray-principal subgroups coincide.
- `rayClassGroupEquivOriginal` and `rayClassGroupEquivOriginalIdele`: isomorphisms from the public ray class group to the library's ideal and idelic ray class groups, sending the class of a prime `v` outside `m` to the class of its prime ideal, respectively to the class of `finitePrimeIdele v`.
- Narrow cases, including `narrowRayClassGroupEquivNarrowClassGroup` with the narrow class group.

## Ray class fields

- `rayClassField_normSubgroup`, `rayClassField_degree`, `rayClassField_reciprocity`: the selected `rayClassField K m` has norm group the ray congruence subgroup of `m`, degree the order of the ray class group, and a Galois group isomorphic to it (a `Nonempty` statement).
- `unramifiedOutsideModulus_of_definingModulus`: a finite abelian `E/K` whose norm group contains the congruence subgroup of `m` is unramified outside `m`, at finite and at real places. Hence `rayClassField_unramifiedOutsideModulus`.
- `embedsInRayClassField_iff_conductor_le`: a finite abelian `L/K` embeds into `rayClassField K m` if and only if its full conductor is at most `m`.
- `rayClassSubgroup_existence`: for a subgroup `H` of a public ray class group there is a `RayClassSubgroupRealization`. This is an extension unramified outside `m` with a surjective Artin map of kernel `H`, sending the class of each prime outside `m` to `arithmeticFrobeniusAt w` for every `w` above it.
- `ClassFieldTheory.normFullConductor_isAbelianConductor`: for abelian `L/K`, the full conductor of the norm group satisfies `IsAbelianConductor K L`: `L` embeds into a ray class field realization for `m` exactly when this conductor is at most `m`. Any realization normalized by Frobenius elements has the ray congruence subgroup as norm group; existence uses `rayClassSubgroup_existence` with the trivial subgroup.

## Points to watch

- Public and library moduli, ray class groups and ray class fields are distinct objects; several statements mix them through `rayClassModulusToOriginal`.
- The conductor here is the full conductor, whose archimedean part is the set of ramified real places, not the narrow finite conductor.
- The deep inputs (norm groups and degrees of ray class fields, the embedding criterion, the realization of subgroups) are imported.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/GlobalClassFields/PublicRayClassComparison.lean`: the Lean file is the source byte for byte (SHA-256 `d512fac8b65c8a8f45c3538413b28666e067a36c8d066ba59739d0ff013006f2`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
