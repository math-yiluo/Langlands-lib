# The small Hilbert class field as an extension of K

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.SmallHilbertClassFieldOverOriginalBase`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The library builds the small Hilbert class field `smallHilbertClassField K` of a number field K over a fixed-field copy `smallHilbertClassFieldBase K` of K, not over K itself. This file uses the ℚ-algebra isomorphism `smallHilbertClassFieldBaseEquiv` between K and that copy as a scalar map. The selected field thereby becomes a finite abelian Galois extension of K. The file says this is the scalar structure later used by extension of ideals in the principal ideal theorem.

## Main definitions and results

- Instances `smallHilbertClassFieldBaseAlgebraOverOriginal` and `smallHilbertClassFieldAlgebraOverOriginal`: K-algebra structures on the copy and on the class field. The scalar map is the base isomorphism followed by inclusion (`smallHilbertClassField_algebraMap_original`). The tower K → copy → class field is a scalar tower.
- `smallHilbertClassFieldBaseEquivOverOriginal`: K ≃ₐ[K] the copy. Hence the copy has degree 1 over K (`smallHilbertClassFieldBase_finrank_over_original`).
- `smallHilbertClassField_finrank_over_original_eq_classNumber`: [`smallHilbertClassField K` : K] equals the class number of K.
- Instances: the class field is finite-dimensional, Galois (`smallHilbertClassFieldIsGaloisOverOriginal`) and abelian Galois (`smallHilbertClassFieldIsAbelianGaloisOverOriginal`) over K.

## Proof

The degree is the index of the closed norm subgroup that defines the class field. This is an imported fact about the closed finite-index class field. The index is the class number by the identification of the quotient with the ideal class group. The Galois and abelian properties are transferred from the copy along the base isomorphism.

## Points to watch

The K-algebra structures are global instances, not local ones, so they apply wherever `smallHilbertClassField K` appears. The field is the library's selected construction, not a field characterized up to isomorphism in this file.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/GlobalClassFields/SmallHilbertClassFieldOverOriginalBase.lean`: the Lean file is the source byte for byte (SHA-256 `4cbba56cfed6b717185c62a33296ca166954db5e2a2a87947e69d00229a9ffce`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
