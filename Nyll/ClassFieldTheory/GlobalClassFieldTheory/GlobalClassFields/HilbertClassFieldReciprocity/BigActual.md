# Reciprocity for the big Hilbert class field over its realized base

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.HilbertClassFieldReciprocity.BigActual`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The file specializes the generic reciprocity transport of `HilbertClassFieldReciprocity.Transport` to the selected big Hilbert class field `bigHilbertClassField K` of a number field `K`, the class field whose Galois group is the narrow ideal class group. This field is constructed as an extension of a concrete base field `bigHilbertClassFieldBase K`, which is identified with `K` by the field isomorphism `bigHilbertClassFieldBaseEquiv`.

## Main results

- `bigHilbertClassField_ideleClassNorm_range_eq_intrinsic`: the image of the idèle-class norm from `bigHilbertClassField K` to its base is the library's intrinsic subgroup `bigHilbertClassFieldNormSubgroup` of the base.
- `bigHilbertClassFieldReciprocityData`: a group isomorphism `Gal(bigHilbertClassField K / bigHilbertClassFieldBase K) ≃* RayClass.NarrowClassGroup K`, bundled with the fact that it sends the global norm-residue symbol of an idèle class `c` to the narrow class of `c` (through `bigHilbertClassFieldQuotientEquivNarrowClassGroup`), transported back to `K` by `bigHilbertNarrowClassGroupCongr`.
- `bigHilbertClassFieldGaloisEquivNarrowClassGroup`: the isomorphism itself.
- `bigHilbertClassFieldGaloisEquivNarrowClassGroup_globalNormResidue` and `bigHilbertClassFieldGaloisEquivNarrowClassGroup_idele` (simp lemmas): its value on the norm-residue symbol of an idèle class, and on that of the class of an idèle `a`, which is the class of `a` modulo `RayClass.narrowDenominator`, transported to `K`.

The norm-range equality combines an earlier computation of the norm range with the compatibility of the intrinsic norm subgroup with `ideleClassCongr`. The isomorphism is `hilbertClassFieldGlobalReciprocityTransportData` applied to that equality and to the identification of the quotient with the narrow class group.

## Points to watch

- The Galois group is taken over `bigHilbertClassFieldBase K`, a field isomorphic to `K` but not `K` itself, while the target is the narrow class group of `K`. The version with `K` as base is in the companion file `HilbertClassFieldReciprocity.BigOriginal`.
- The isomorphism comes from the library's `globalReciprocityEquiv`; the file adds no reciprocity argument of its own. The big Hilbert class field, its base and its norm subgroup are the library's own constructions, made in imported files.
- Commutativity of the idèle class group is supplied by a local instance.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/GlobalClassFields/HilbertClassFieldReciprocity/BigActual.lean`: the Lean file is the source byte for byte (SHA-256 `ab5c8b7dfeeb93dcaa85cd81344e1824e8a1664bf715b63ef01e35cc0f06a74b`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
