# Cyclic norm subgroups that are congruence subgroups at their conductor

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.CyclicRayClassMaximality`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let L/K be a finite cyclic extension of number fields, N its idèle-class norm subgroup, and f the narrow finite conductor of N. The ray class group modulo f, with positivity at all real places, maps onto C_K/N, of order [L : K]. In the cyclic case, this map is an isomorphism exactly when the ray class number at f equals [L : K].

- `ideleClassNorm_range_eq_narrowConductorSubgroup_iff_rayClass_card_eq_degree`: N equals the congruence subgroup at f if and only if the ray class number at f is [L : K].
- `narrowFiniteConductorRayClassGroupToIdeleClassNormQuotient_injective_iff_card_eq_extensionDegree`: the canonical map to C_K/N is injective under the same condition.
- `cyclicNormQuotientEquivNarrowFiniteConductorRayClassGroup`: given that condition (hypothesis `hcard`), C_K/N is isomorphic to the ray class group at f.

The proofs substitute the cyclic norm index equality `ClassFieldAxiom.ideleClassNorm_index_eq_finrank_cyclic` into the general statements of the imported norm ray-class maximality file.

## Points to watch

- `hcard` is a real restriction. It holds exactly when N is the whole congruence subgroup at f, so the isomorphism is not available in general.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/GlobalClassFields/CyclicRayClassMaximality.lean`: the Lean file is the source byte for byte (SHA-256 `719bcc1e756fb9d9e5e35f4cc38fb46c5595f866f99c55774eead5af8dfd0641`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
