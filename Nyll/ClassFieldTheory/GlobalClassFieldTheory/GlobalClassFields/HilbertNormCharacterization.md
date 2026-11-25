# Norm subgroups of extensions unramified at finite primes

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.HilbertNormCharacterization`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The file gives the norm-subgroup form of the maximality of the big (narrow) Hilbert class field. For a finite Galois extension `L/K` of number fields in which no finite prime of `K` ramifies, the idèle-class norm range of `L` contains the big Hilbert norm subgroup of `K`. The resulting surjection from the narrow class group onto the norm quotient bounds the size of that quotient and, for cyclic `L/K`, the degree.

## Main results

Throughout, `L/K` is finite Galois and `hunramified` says that `ramifiedBaseFinitePlaces` is empty.

- `ideleClassNorm_narrowFiniteConductor_eq_zero_of_no_ramifiedFinitePlaces`: the narrow finite conductor of the norm subgroup is zero, since its support lies among the ramified finite primes.
- `bigHilbertClassFieldNormSubgroup_le_ideleClassNorm_range_of_no_ramifiedFinitePlaces`: `bigHilbertClassFieldNormSubgroup ≤` the image of `ideleClassNorm K L`, by the imported criterion that the big Hilbert norm subgroup lies in a conductorial subgroup exactly when its narrow finite conductor vanishes.
- `bigHilbertClassFieldQuotientToIdeleClassNormQuotient`: the induced map `C_K ⧸ H ⟶ C_K ⧸ N(C_L)`, with `H` the big Hilbert norm subgroup; it is surjective, sends a class to the same class (`_mk`), and its kernel is the image of the norm range (`_ker`). `bigHilbertNormImageQuotientEquivIdeleClassNormQuotient` is the resulting isomorphism.
- `narrowClassGroupToIdeleClassNormQuotient`: the surjection `RayClass.NarrowClassGroup K ⟶ C_K ⧸ N(C_L)` through `bigHilbertClassFieldQuotientEquivNarrowClassGroup`, and `narrowClassGroupToIdeleClassNormQuotient_surjective`.
- `ideleClassNormQuotient_card_dvd_narrowClassGroup_card_of_no_ramifiedFinitePlaces`: the order of `C_K ⧸ N(C_L)` divides the narrow class number.
- `narrowClassGroup_card_eq_unramifiedNormKernel_card_mul_normQuotient_card`: the narrow class number is the order of the kernel of this surjection times the order of the norm quotient.
- With `[IsCyclic (L ≃ₐ[K] L)]`: `cyclicExtensionDegree_dvd_narrowClassGroup_card_of_no_ramifiedFinitePlaces` (`[L : K]` divides the narrow class number) and `narrowClassGroup_card_eq_unramifiedCyclicNormKernel_card_mul_extensionDegree` (the narrow class number is the kernel order times `[L : K]`). These use the imported equality of the norm index with the degree for abelian extensions.

## Points to watch

- Only finite primes are assumed unramified; infinite places may ramify, which is why the narrow class group appears.
- This is an inclusion of norm subgroups, not a containment of fields: no embedding of `L` into the big Hilbert class field is constructed here.
- The first results need only `IsGalois`; the statements about `[L : K]` need a cyclic Galois group.
- Orders are `Nat.card`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/GlobalClassFields/HilbertNormCharacterization.lean`: the Lean file is the source byte for byte (SHA-256 `7e9840f1dc39c298a48aa5c31026a5d223e704ac745f34edb6c5abf9b5a179a0`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
