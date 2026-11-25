# The kernel of maximal abelian global reciprocity

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.MaximalAbelianKernel`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a number field `K`, this file proves that the kernel of the global Artin map `maximalAbelianGlobalArtin K : C_K → Gal(Kᵃᵇ / K)` is the identity component `D_K` of the idèle class group, and descends the map to an isomorphism of topological groups `C_K / D_K ≃ Gal(Kᵃᵇ / K)`.

## Main results

- `exists_closedFiniteIndexSubgroup_not_mem_of_not_mem_identityComponent`: a class `c ∉ D_K` lies outside some closed subgroup of finite index of `C_K` that contains `D_K`.
- `finiteAbelianExtensionInMaximalAbelianExtension_ideleClassNorm_range`: replacing a finite abelian extension `L / K` by its isomorphic copy inside `Kᵃᵇ` does not change the norm range, the range of `ideleClassNorm K L`.
- `maximalAbelianGlobalArtin_ker`: the kernel of `maximalAbelianGlobalArtin K` is `ideleClassIdentityComponent K`.
- `ideleClassComponentQuotientEquivMaximalAbelianGalois`: the induced isomorphism of topological groups from `C_K / D_K` onto `Gal(Kᵃᵇ / K)`; `..._mk` evaluates it on the class of `c` as `maximalAbelianGlobalArtin K c`.

## Proofs

The separation lemma works in the quotient `C_K / D_K`, treated as a profinite group: an open normal subgroup inside the complement of the image of `c` is pulled back to `C_K`. For the kernel, the inclusion of `D_K` comes from `ideleClassIdentityComponent_le_ker`. Conversely, if `c` is in the kernel but not in `D_K`, take the subgroup `H` above and its class field `closedFiniteIndexClassField H`, whose norm range is `H`. The finite Artin map of the copy `E` of this field in `Kᵃᵇ` kills `c`, so `c` lies in the norm range of `E` by `globalIdeleClassArtinMonoidHom_eq_one_iff`, that is in `H`: a contradiction. Continuity of the inverse comes from compactness of the source and Hausdorffness of the target.

## Remarks

- The proof rests on the existence theorem in the form of `closedFiniteIndexClassField` and `closedFiniteIndexClassField_ideleClassNorm_range`, and on finite reciprocity (kernel of the finite Artin map equals the norm range), both from imported files.
- `C_K` is the library's own `IdeleClassGroup K`, not Mathlib's.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/Reciprocity/MaximalAbelianKernel.lean`: the Lean file is the source byte for byte (SHA-256 `58109f7b9e673d1083d4bd36a92bec822a7901970db15af90e35945a9fa6644a`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
