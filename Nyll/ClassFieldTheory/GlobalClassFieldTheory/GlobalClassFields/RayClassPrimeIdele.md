# Prime idèles and ideal ray classes

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.RayClassPrimeIdele`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a number field `K` and a prime `v`, the library's normalized prime idèle `finitePrimeIdele v` is concentrated at `v`, with component `1` at every other place. The file shows that it represents the prime ideal of `v` in both the idelic and the ideal-theoretic ray class groups. It then identifies the ideal-theoretic Frobenius classes for the two Hilbert norm subgroups with the library's Hilbert Frobenius classes.

## Main results

Let `m` be a modulus (`RayClass.Modulus`) and `v` a prime outside its finite support.

- `finitePrimeIdele_mem_idelePrimeToModulusSubgroup`: the prime idèle of `v` is prime to `m`.
- `primeToIdealMap_finitePrimeIdele` and `idealRayProjection_finitePrimeIdele`: its fractional ideal is the prime ideal of `v`, and its ideal ray class is the class of that prime.
- `rayClassGroupEquivIdeleQuotient_mk_mk`: `RayClass.rayClassGroupEquivIdeleQuotient` sends the double class of any idèle to its class modulo the join of the idèle congruence subgroup of `m` and the principal idèles. `rayClassGroupEquivIdealRayClassGroup_mk_primeTo`: on representatives, the isomorphism from the idelic to the ideal ray class group sends an idèle prime to `m` to the ray class of its fractional ideal.
- `idealArtinMap_primeToIdealMap`: for a subgroup `N` of the idèle class group containing the congruence subgroup of `m`, the ideal Artin map sends the ideal of an idèle prime to `m` to the class of that idèle modulo `N`. `idealFrobeniusClass_eq_finitePrimeIdeleClass` is the case of a prime.
- Big Hilbert case, with `m` the narrow modulus with zero finite part. `bigHilbertIdealFrobeniusClass_eq_bigHilbertFrobeniusClass`: the ideal Frobenius class for `bigHilbertClassFieldNormSubgroup` is `bigHilbertFrobeniusClass v`. Its order is that of the narrow class of `v` (`orderOf_bigHilbertIdealFrobeniusClass`). It is trivial exactly when the prime ideal of `v` has a generator whose principal idèle is prime to the narrow modulus, a totally positive generator (`bigHilbertIdealFrobeniusClass_eq_one_iff_exists_totallyPositiveGenerator`).
- Small Hilbert case, with `m = 0`. `smallHilbertIdealFrobeniusClass_eq_smallHilbertFrobeniusClass`: it is `smallHilbertFrobeniusClass v`, its order is that of the ideal class of `v`, and it is trivial exactly when the prime ideal is principal (`smallHilbertIdealFrobeniusClass_eq_one_iff_principal`).

The Hilbert cases reduce, through the prime-idèle formula, to the isomorphisms of the Hilbert norm quotients with the narrow and ordinary class groups. The triviality criteria are imported results on the Hilbert Frobenius classes.

## Points to watch

- These Frobenius classes are classes in idèle-class quotients, not Galois automorphisms; no Galois group appears in this file.
- In the big Hilbert criterion, total positivity is expressed as membership of the principal idèle in the prime-to-modulus subgroup of the narrow modulus.
- A normality witness for the quotients, `IdealClassFieldTheory.ideleClassSubgroupNormal`, is used as a local instance.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/GlobalClassFields/RayClassPrimeIdele.lean`: the Lean file is the source byte for byte (SHA-256 `497db857c9d210f68bbe3b6e07a03bb0decf0a0021b4a3d5edf1f04c8105c412`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
