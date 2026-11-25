# Naturality of the small Hilbert norm subgroup

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.SmallHilbertClassFieldNaturality`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let e : K ≃ₐ[ℚ] M be an isomorphism of number fields. This file shows that the induced isomorphism of idele class groups preserves the small-Hilbert norm subgroup, the image of the ideles whose finite components are all local units. It then transports the quotient by this subgroup, and with it the ideal class group, along e.

## Main definitions and results

- `smallHilbertClassFieldNormSubgroup_map_ideleClassCongr`: the image of the small-Hilbert norm subgroup of K under `ideleClassCongr e` is the small-Hilbert norm subgroup of M.
- `smallHilbertClassFieldQuotientCongr e`: the induced isomorphism of quotients C_K/H_K ≃* C_M/H_M. On representatives it is `ideleClassCongr e` (`smallHilbertClassFieldQuotientCongr_mk`).
- `smallHilbertClassGroupCongr e`: the isomorphism `ClassGroup (𝓞 K) ≃* ClassGroup (𝓞 M)` obtained by conjugating the quotient isomorphism with the identifications of each quotient with the class group.
- `smallHilbertClassFieldQuotientEquivClassGroup_naturality`, with its homomorphism form `..._naturality_hom`: these identifications commute with the two transports.
- `smallHilbertClassGroupCongr_idealClass` and `smallHilbertClassGroupCongr_naturality`: the ideal class of an idele a goes to the ideal class of `ideleCongr e a`.

## Proof

The first statement comes from an imported result on transporting the ordinary ideal-class subgroup. The rest unfolds the definitions.

## Points to watch

`smallHilbertClassGroupCongr` is defined through the idele quotients. The file identifies it with transport of ideal classes only on classes of ideles, `IdeleGroup.idealClass`. It does not compare it with Mathlib's map on ideals.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/GlobalClassFields/SmallHilbertClassFieldNaturality.lean`: the Lean file is the source byte for byte (SHA-256 `fbe9a434a4c33183526a6f34e805125ed28e3153e839e8505910892a6a1148d0`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
