# Rigidity of Frobenius-normalized ray class reciprocity

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.RayFrobeniusRigidity`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `L/K` be a finite abelian extension of number fields and `m` a modulus of `K`. Suppose a homomorphism from the ray class group of `m` to `Gal(L/K)` sends the class of every prime `v` outside `m` to the arithmetic prime Artin element of `v`. The file shows that this condition determines the homomorphism completely: it is induced by the arithmetic global norm-residue map. Consequently `m` is a defining modulus for the norm group of `L`.

## Main results

In each statement `hprime` says that the class of the prime idèle `finitePrimeIdele v` goes to `arithmeticFinitePlacePrimeArtin v` for every finite prime `v` outside the support of `m`.

- `rayArtin_comp_ideleClass_eq_arithmeticGlobalNormResidue`: for a homomorphism `artin` satisfying `hprime`, the image of the ray class of any idèle class `x` is the arithmetic global norm-residue symbol of `x`. This includes classes supported at primes dividing `m`.
- `rayModulus_normSubgroup_eq_artinKer_preimage`: under the same hypothesis, the norm group `N(C_L)` is the preimage in `C_K` of the kernel of `artin`. The map need not be injective.
- `rayModulus_isDefining_of_arithmeticPrimeArtinEquiv`: if `e` is an isomorphism satisfying `hprime`, the ray congruence subgroup of `m` lies in `N(C_L)`.
- `rayModulus_normSubgroup_eq_of_arithmeticPrimeArtinEquiv`: for such an isomorphism, `N(C_L)` equals the ray congruence subgroup. The induced map from the ray class group onto `C_K ⧸ N(C_L)` is a surjection between finite groups of the same order.

## Proof

Let `n` be the least common multiple of `m` and the full conductor of `L/K`. Two homomorphisms from the ray class group of `n` to `Gal(L/K)` are compared: global reciprocity, and the given map composed with the projection to the ray class group of `m`. They agree on prime classes outside `n` by `hprime` and the imported evaluation of the norm-residue map on prime idèles. The imported lemma `rayClassGroup_hom_ext_finitePrime` says such classes determine a homomorphism, so the two maps agree. Pulled back to `C_K`, the kernel of the given map is that of the arithmetic norm-residue map, which is `N(C_L)` by an imported result.

## Points to watch

- The normalization is arithmetic: `hprime` is stated with the library's arithmetic prime Artin element, not with Mathlib's Frobenius or the geometric prime Artin element.
- The equality of norm groups needs an isomorphism; a mere homomorphism gives only the kernel description.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/GlobalClassFields/RayFrobeniusRigidity.lean`: the Lean file is the source byte for byte (SHA-256 `be9c436af2551087b3cdbb6c0a973e95d158f19c6d0228cb2b60622948cea997`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
