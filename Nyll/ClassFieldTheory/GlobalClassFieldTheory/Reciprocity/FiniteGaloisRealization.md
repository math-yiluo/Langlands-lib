# Norm groups of a realized finite Galois tower of number fields

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FiniteGaloisRealization`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let L/K be a finite Galois extension of number fields. Elsewhere the library realizes it inside ℚ̄ = `SeparableClosure ℚ`: closed subgroups J ≤ H of Gal(ℚ̄/ℚ) (`numberFieldTowerTopSubgroup L`, `numberFieldTowerBaseSubgroup K L`); the fixed field F of H is isomorphic to K, and the fixed field E of J to L. This file gives F and E the number-field instances needed by the rational idele-class formation. It then shows that, under this realization, the abstract finite norm group of the class formation is the ordinary norm group of idele classes, the image of C_L under the norm from L to K.

## Main results

- `realizedTowerIdeleClassCommGroup`: fixes the group structure on `IdeleClassGroup F` as the quotient by the principal ideles, with commutativity as a local instance.
- `numberFieldTowerFiniteNormQuotientEquivIdeleClassNormQuotient_finiteNormClass` (simp): the comparison equivalence (defined in an imported file) sends the finite norm class of a fixed-part element a to the class, modulo the range of `ideleClassNorm K L`, of the idele class of K matching a.
- `numberFieldTowerFiniteNormQuotientEquivIdeleClassNormQuotient_ideleClass` (simp): the same for an idele class c of K: the result is the class of c in C_K modulo that norm group.
- `map_numberFieldTowerFiniteNormSubgroup_eq_ordinaryIdeleClassNormRange`: transported back to C_K, the abstract `finiteNormSubgroup` for J ≤ H is exactly the range of `ideleClassNorm K L`.
- `numberFieldTowerTransport_isNormOpen_of_normRange_le`: a subgroup of C_K containing that norm group is carried to a subgroup that is open for the norm topology of the class formation (`IsNormOpen`), with the realized L as witness.

## Proof

The first identity is a chain of three private steps. The comparison is first unfolded to a direct comparison through the fixed fields F, E. That direct comparison is then evaluated on finite norm classes with `rationalFiniteNormQuotientEquivIdeleClassNormQuotient_finiteNormClass`. Finally `ordinaryIdeleClassNormQuotientCongrOfAlgEquiv` moves the result along the isomorphisms K ≅ F, L ≅ E. The norm-subgroup equality follows, because a finite norm class vanishes exactly on the norm subgroup (`finiteNormClass_eq_zero_iff`).

## Points to watch

- The module heading speaks of transporting reciprocity. The declarations here compare norm quotients and norm subgroups only; no reciprocity map is defined or compared in this file.
- `ideleClassNorm` and `IdeleClassGroup` are the library's own constructions, not Mathlib's.
- The openness result gives one direction only: subgroups containing a norm group are norm-open. The converse is not stated here.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/Reciprocity/FiniteGaloisRealization.lean`: the Lean file is the source byte for byte (SHA-256 `79b54b6b7619d6c2f62a02ffa4a22e8d85402ddd5e148fdcddcb7694a2841c5f`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
