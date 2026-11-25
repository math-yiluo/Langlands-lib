# Global class field theory: the public statements

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.MathlibGlobalReciprocity`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The file supports the reader-facing statements of global class field theory for number fields. It collects finite and maximal abelian reciprocity, the existence theorem for class fields, and an Artin map on a ray class group at the norm conductor. Most results restate constructions made in imported files in the public vocabulary of ray class moduli (`RayClassModulus`, `RayClassGroup`).

## Main definitions and results

- `exists_unramifiedOutsideModulus`: for any extension `L/K` of number fields there is a modulus outside which `L/K` is unramified. Its finite part has exponent 1 at each ramified prime (a finite set), and its infinite part is every real place.
- `normConductorRayClassModulus K L`, for `L/K` abelian: the modulus whose finite part is the narrow finite conductor of the idèle-class norm subgroup, `ideleClassNormNarrowFiniteConductor`, and whose infinite part is every real place. `normConductorRayClassModulus_original` identifies it with the library's `RayClass.Modulus.narrowOfFinite` of that conductor. `normConductorRayClassModulus_unramifiedOutside` and `unramifiedOutside_normConductorModulus` say `L/K` is unramified outside it.
- `normConductorArtin K L`: a homomorphism from the ray class group of this modulus to `L ≃ₐ[K] L`. It is built from the library's ideal ray class Artin map and the arithmetic global norm-residue isomorphism `arithmeticGlobalNormResidueContinuousMulEquiv`. `normConductorArtin_surjective`: it is onto. `normConductorArtin_prime`: a prime `v` outside the conductor maps to the arithmetic prime Artin element `arithmeticFinitePlacePrimeArtin v`.
- `classFieldExistence_normSubgroup`, `classFieldExistence_degree`: for a closed subgroup `H` of finite index in the idèle class group, the library's selected class field `closedFiniteIndexClassField H` has norm group exactly `H` and degree the index of `H`.
- `finiteAbelianGlobalReciprocity`: for finite abelian `L/K` there exists an isomorphism of topological groups between `C_K ⧸ N(C_L)` and `Gal(L/K)`.
- `maximalAbelianGlobalReciprocity`: there exists an isomorphism of topological groups between the idèle class group modulo its identity component and the Galois group of `maximalAbelianExtension K`.
- `ideleClassGroupIsMulCommutative`: commutativity of the idèle class group, installed as a local instance of priority 2000.

## Points to watch

- The reciprocity and existence results are imported constructions repackaged here, the two reciprocity theorems as `Nonempty` statements. The file proves only the bookkeeping on moduli and the evaluation at primes.
- `normConductorRayClassModulus` always contains every real place, ramified or not, so it is a narrow modulus. It is not the usual conductor, which contains only the ramified real places.
- The modulus of `exists_unramifiedOutsideModulus` controls ramification only; it is not claimed to define the norm subgroup.
- The public `RayClassModulus` and `RayClassGroup` are distinct from the library's internal `RayClass.Modulus`; the bridge is `rayClassModulusToOriginal` and `rayClassGroupEquivOriginal`.
- The Artin map uses the arithmetic normalization.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/GlobalClassFields/MathlibGlobalReciprocity.lean`: the Lean file is the source byte for byte (SHA-256 `68757bae0d797d25ed06b1f727c7deb7e571197e33fdadb1291431417aad36b7`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
