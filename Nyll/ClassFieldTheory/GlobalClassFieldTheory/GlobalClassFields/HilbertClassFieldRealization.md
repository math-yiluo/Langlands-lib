# Selected big and small Hilbert class fields

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.HilbertClassFieldRealization`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a number field K, the big Hilbert norm subgroup (quotient the narrow class group Cl⁺(K)) and the small Hilbert norm subgroup (quotient the class group Cl(K)) of the idèle class group C_K are closed and of finite index. This file applies the library's class field construction for closed subgroups of finite index to both. That construction produces a field inside ℚ̄ = `SeparableClosure ℚ`. The file fixes the resulting fields once and for all, identifies their norm groups, and computes their degrees.

## Main definitions and results

- `bigHilbertClassFieldNormAmbient` and `smallHilbertClassFieldNormAmbient`: the finite Galois norm neighbourhoods from which the two class fields are cut out.
- `bigHilbertClassFieldBaseSubgroup`, `bigHilbertClassFieldSubextension`, `bigHilbertClassFieldBase`, `bigHilbertClassField` and `bigHilbertClassFieldBaseEquiv`: the base subgroup of Gal(ℚ̄/ℚ), the selected finite abelian subextension, the copy F of K inside ℚ̄ with its isomorphism K ≃ₐ[ℚ] F, and the field itself. The small Hilbert analogues carry the prefix `smallHilbertClassField`.
- `bigHilbertClassFieldTransportedNormSubgroup` and `bigHilbertClassField_ideleClassNorm_range`: the norm group of the big Hilbert class field over F is the big Hilbert subgroup transported from C_K to C_F.
- `bigHilbertClassField_finrank_eq_narrowClassGroup_card`: its degree over F is |Cl⁺(K)|.
- `smallHilbertClassFieldTransportedNormSubgroup`, `smallHilbertClassField_ideleClassNorm_range` and `smallHilbertClassField_finrank_eq_classNumber`: the same for the small Hilbert class field, whose degree is h_K.

## Proof

The norm-group identification is the imported `closedFiniteIndexClassField_ideleClassNorm_range_over_base`. The degree equals the index of the norm group by the abelian norm index theorem (`ideleClassNorm_index_eq_finrank_abelian`). That index is preserved under transport, and it equals the order of the reciprocity quotient.

## Points to watch

- In this file, norm groups and degrees are stated over the copy F of K inside ℚ̄, not over K itself, and comparison with K goes through `bigHilbertClassFieldBaseEquiv` (respectively `smallHilbertClassFieldBaseEquiv`).
- These are particular choices produced by the construction, fixed as abbreviations, not fields characterized up to isomorphism in this file.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/GlobalClassFields/HilbertClassFieldRealization.lean`: the Lean file is the source byte for byte (SHA-256 `14c7c31910e3292732422e9ac5ad1626bb9aef8e53a210b5ac34a30b418f6676`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
