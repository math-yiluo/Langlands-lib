# The norm quotient of a realized tower L/K

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FiniteGaloisRealizationNormQuotient`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let L/K be a finite Galois extension of number fields, realized inside ℚ̄ = `SeparableClosure ℚ` by the compatible embeddings of the library, with closed subgroups J ≤ H of Gal(ℚ̄/ℚ) fixing the copies of L and K. The file identifies the fixed fields of H and J with K and L. It then shows that the abstract finite norm quotient of the rational idele-class formation for J ≤ H is isomorphic to the ordinary norm quotient, C_K modulo the image of the idele-class norm from L.

## Main definitions and results

- `numberFieldTowerAbstractBaseField_eq` and `numberFieldTowerAbstractTopField_restrictScalars_eq`: the fixed field of H is the copy of K, and the relative fixed field of J ≤ H, viewed over ℚ, is the copy of L.
- `numberFieldTowerAbstractBaseFieldEquiv K L : K ≃ₐ[ℚ] F` and `numberFieldTowerAbstractTopFieldEquiv K L : L ≃ₐ[ℚ] E`, compatible with the algebra maps K → L and F → E (`numberFieldTowerAbstractFieldEquiv_algebraMap`, simp).
- Instances recording that H has finite index in Gal(ℚ̄/ℚ), that the extension subgroup of J in H is normal, and that the quotient is finite. Local instances make F and E number fields through K and L, and fix the group structures on the idele class groups and on the norm quotient.
- `numberFieldTowerIdeleClassEquivAmbientFixed K L`: the idele class group of K, written additively, is isomorphic to the H-fixed part of `rationalIdeleClassRepresentation`. This goes through F by `ideleClassCongr` and `rationalAbstractFixedFieldIdeleClassEquivFixed`.
- `numberFieldTowerFiniteNormQuotientEquivIdeleClassNormQuotient K L`: an additive isomorphism from `FiniteNormQuotient rationalIdeleClassRepresentation H J _` to C_K modulo the range of `ideleClassNorm K L`. It is the composite of two named steps. `numberFieldTowerFiniteNormQuotientEquivFixedFieldNormQuotient` goes from the abstract quotient to C_F modulo the image of the norm from C_E (`rationalFiniteNormQuotientEquivIdeleClassNormQuotient`). `numberFieldTowerFixedFieldNormQuotientEquivActualNormQuotient` goes back along K ≅ F, L ≅ E (`ordinaryIdeleClassNormQuotientCongrOfAlgEquiv`).

## Points to watch

- The module heading also mentions transporting reciprocity data. This file transports only the norm quotient and the idele class group; no reciprocity map appears.
- `numberFieldTowerFixedFieldNormQuotient` is a separate type definition. It wraps the fixed-field norm quotient so that the two comparison steps elaborate separately.
- `IdeleClassGroup` and `ideleClassNorm` are the library's own constructions. The group structure on the idele class group is fixed here as the quotient by `IdeleGroup.principalSubgroup`.
- Everything depends on the chosen embedding of L into ℚ̄, with K embedded through L.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/Reciprocity/FiniteGaloisRealizationNormQuotient.lean`: the Lean file is the source byte for byte (SHA-256 `95834a24ac0da07d10b6bd5d632034d7cb4153bd6ef50fa3bf9254ab4dbff7f6`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
