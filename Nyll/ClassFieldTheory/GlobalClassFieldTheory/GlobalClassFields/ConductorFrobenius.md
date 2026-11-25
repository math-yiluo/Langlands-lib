# Prime classes at the narrow finite norm conductor

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ConductorFrobenius`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let L/K be a finite Galois extension of number fields, N the image of the idèle class norm, and f the exact narrow finite conductor of N (the library's `ideleClassNormNarrowFiniteConductor`). For a finite prime v, the one-place idèle of normalized order one at v (`finitePrimeIdele v`) gives a prime class in the ray class group modulo f (with all real places positive) and a prime class in C_K/N. This file compares the two classes and relates them to complete splitting and to the ideal Artin map.

## Main definitions and results

- `narrowFiniteConductorRayPrimeClass v` and `ideleClassNormFrobeniusClass v`: the two classes. The canonical map from the ray class group to C_K/N sends the first to the second (`narrowFiniteConductorRayClassGroupToIdeleClassNormQuotient_rayPrimeClass`). So the order of the second divides the order of the first.
- `narrowFiniteConductorIdealFrobeniusClass_eq_ideleClassNormFrobeniusClass`: for v outside the support of f, the ideal-theoretic Frobenius class of v equals the class in C_K/N. Hence that class has the order of the prime ideal modulo the ideal Artin kernel, and is trivial exactly when the prime ideal lies in that kernel.
- `finitePlaceSplitsCompletely_imp_ideleClassNormFrobeniusClass_eq_one`: if v splits completely in L, its class in C_K/N is trivial. The ideal-theoretic forms follow.
- Under the hypothesis `hcard` that the ray class group modulo f and C_K/N have the same cardinality, the canonical map is injective. Then the ray prime class is trivial exactly when the norm-quotient class is, and both classes have the same order.
- For cyclic L/K, `orderOf_ideleClassNormFrobeniusClass_dvd_extensionDegree` says that the order of the norm-quotient class divides [L : K]; the same holds for the ideal Frobenius class and the ideal Artin prime class.
- For cyclic L/K, with `hcard` in the form "the ray class group modulo f has [L : K] elements": a completely split v has trivial ray prime class, and triviality is equivalent to membership in the ideal Artin kernel.
- `orderOf_narrowFiniteConductorRayPrimeClass_dvd_extensionDegree_of_card_eq`: under that form of `hcard`, without cyclicity, the order of every ray prime class divides [L : K].

## Proof

The cyclic results use the index equality [C_K : N] = [L : K] (`ClassFieldAxiom.ideleClassNorm_index_eq_finrank_cyclic`).

## Points to watch

- The conductor is the narrow finite one: real places always carry the positivity condition, and no archimedean part of the conductor is computed.
- Apart from the divisibility in the first item, the conclusions about the ray prime class depend on the cardinality hypothesis `hcard`. It asserts that the ray class group modulo the conductor is no larger than C_K/N, which is a genuine restriction rather than a general fact.
- The ideal-theoretic comparisons hold only for primes outside the support of f (hypothesis `hv`).

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/GlobalClassFields/ConductorFrobenius.lean`: the Lean file is the source byte for byte (SHA-256 `03045ba78b885782af89241d3f2653fdfa32f50bd7e13811609f7b4626c4b1d4`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
