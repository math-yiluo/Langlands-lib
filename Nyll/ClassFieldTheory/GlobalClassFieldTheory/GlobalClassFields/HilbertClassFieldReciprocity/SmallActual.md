# Reciprocity for the small Hilbert class field over its realized base

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.HilbertClassFieldReciprocity.SmallActual`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The file specializes the generic reciprocity transport of `HilbertClassFieldReciprocity.Transport` to the selected small Hilbert class field `smallHilbertClassField K` of a number field `K`, the class field whose Galois group is the ordinary ideal class group `ClassGroup (𝓞 K)`. This field is constructed as an extension of a concrete base field `smallHilbertClassFieldBase K`, identified with `K` by the field isomorphism `smallHilbertClassFieldBaseEquiv`.

## Main results

- `smallHilbertClassField_ideleClassNorm_range_eq_intrinsic`: the image of the idèle-class norm from `smallHilbertClassField K` to its base is the library's intrinsic subgroup `smallHilbertClassFieldNormSubgroup` of the base.
- `smallHilbertClassFieldReciprocityData`: a group isomorphism `Gal(smallHilbertClassField K / smallHilbertClassFieldBase K) ≃* ClassGroup (𝓞 K)`, bundled with the fact that it sends the global norm-residue symbol of an idèle class `c` to the ideal class of `c` (through `smallHilbertClassFieldQuotientEquivClassGroup`), transported back to `K` by `smallHilbertClassGroupCongr`.
- `smallHilbertClassFieldGaloisEquivClassGroup`: the isomorphism itself.
- `smallHilbertClassFieldGaloisEquivClassGroup_globalNormResidue` and `smallHilbertClassFieldGaloisEquivClassGroup_idele` (simp lemmas): its value on the norm-residue symbol of an idèle class, and on that of the class of an idèle `a`, which is the ideal class `IdeleGroup.idealClass a`, transported to `K`.

The norm-range equality combines an earlier computation of the norm range with the compatibility of the intrinsic norm subgroup with `ideleClassCongr`. The isomorphism is `hilbertClassFieldGlobalReciprocityTransportData` applied to that equality and to the identification of the quotient with the class group.

## Points to watch

- The Galois group is taken over `smallHilbertClassFieldBase K`, a field isomorphic to `K` but not `K` itself, while the target is the class group of `K`. The version with `K` as base is in the companion file `HilbertClassFieldReciprocity.SmallOriginal`.
- The isomorphism comes from the library's `globalReciprocityEquiv`; the file adds no reciprocity argument of its own. The small Hilbert class field, its base and its norm subgroup are the library's own constructions, made in imported files.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/GlobalClassFields/HilbertClassFieldReciprocity/SmallActual.lean`: the Lean file is the source byte for byte (SHA-256 `d6a7ca84a8e6461afe5a2f2b72c169605cfe289f845ec1161913e88bc84eb657`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
