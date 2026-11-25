# Ray class number at the conductor of a cyclic extension

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.CyclicNormConductor`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let L/K be a finite cyclic extension of number fields, N its idèle-class norm subgroup (the image of C_L in C_K under the norm), and f the narrow finite conductor of N (`ideleClassNormNarrowFiniteConductor`). This file inserts the norm index equality [C_K : N] = [L : K] into the factorization of the ray class number at f.

- `narrowFiniteConductorRayClassGroup_card_eq_normSubgroupImage_card_mul_extensionDegree`: the order of the ray class group modulo f, with positivity at all real places, equals the order of the image of N in that group times [L : K].
- `cyclicExtensionDegree_dvd_narrowFiniteConductorRayClassGroup_card`: [L : K] divides this ray class number.

Both follow from the corresponding general statements for C_K/N, together with the norm index theorem for abelian extensions, `Reciprocity.ideleClassNorm_index_eq_finrank_abelian`, applied through the abelian structure of a cyclic extension.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/GlobalClassFields/CyclicNormConductor.lean`: the Lean file is the source byte for byte (SHA-256 `fcbf7347a0c795f0e472a7145ed834c59555316a236dbc0807fc9401acb8d744`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
