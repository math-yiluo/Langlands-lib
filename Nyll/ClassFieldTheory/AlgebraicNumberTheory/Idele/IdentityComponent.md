# The identity component of the idele class group

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.IdentityComponent`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a number field `K`, the file studies the connected component `D_K` of the identity in the idele class group `C_K`. It shows that `D_K` is a closed normal subgroup and that the quotient `C_K / D_K` is a compact, Hausdorff, totally disconnected group. It also shows that `D_K` lies in the kernel of every continuous homomorphism from `C_K` to a totally disconnected topological group.

## Main declarations

- `ideleClassIdentityComponent K`: the identity component as a subgroup. It is closed (`ideleClassIdentityComponent_isClosed`) and normal (an instance).
- `ideleClassComponentQuotient K`: the quotient `C_K / D_K`, with instances `T2Space`, `TotallyDisconnectedSpace` and `CompactSpace`.
- `ideleClassPositiveArchimedeanSection`, and its continuous form `ideleClassPositiveArchimedeanSectionContinuous`: the section `ℝ≥0ˣ → C_K` induced by `IdeleGroup.positiveArchimedeanSection`. Its values lie in `D_K`, because the positive reals are connected (`ideleClassPositiveArchimedeanSection_mem_identityComponent`), and the absolute norm of the value at `r` is `r⁻¹`.
- `ideleClassNormOneCorrection` and `ideleClass_mk_eq_normOneCorrection_mul_positiveSection_inv`: every idele class is a norm-one class times the inverse of the section at its absolute norm.
- `ideleClassNormOneToComponentQuotient`: the continuous map from the norm-one classes `C_K¹` to `C_K / D_K`. It is surjective (`ideleClassNormOneToComponentQuotient_surjective`), since the section part dies in the quotient.
- `ideleClassIdentityComponent_le_ker`: every continuous homomorphism `C_K → H`, with `H` totally disconnected, vanishes on `D_K`.

## Proof

Compactness of `C_K / D_K` holds because it is the continuous image of `C_K¹`. Total disconnectedness and the Hausdorff property are general facts about quotients by the identity component.

## Points to watch

- Compactness rests on the compactness of the norm-one idele classes `C_K¹`, which this file takes from an imported file.
- `D_K` is only defined here as the identity component; no further description of it is given.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Idele/IdentityComponent.lean`: the Lean file is the source byte for byte (SHA-256 `aa680228f662b8dc134a25e4ae5b7ca42cfaad43bbd63009d233c86193a096e8`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
