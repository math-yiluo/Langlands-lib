# Reciprocity for the big Hilbert class field over the original field

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.HilbertClassFieldReciprocity.BigOriginal`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The file states global reciprocity for the selected big Hilbert class field `bigHilbertClassField K` of a number field `K`, regarded as an extension of `K` itself rather than of the realized base field `bigHilbertClassFieldBase K` used in `HilbertClassFieldReciprocity.BigActual`. The Galois group is identified with the narrow ideal class group of `K` with no transport left over.

## Main results

- `bigHilbertClassField_ideleClassNorm_range_over_original`: with `bigHilbertClassField K` viewed as a `K`-algebra, the image of the idèle-class norm is `bigHilbertClassFieldNormSubgroup (K := K)`.
- `bigHilbertClassFieldReciprocityOverOriginalData` and `bigHilbertClassFieldGaloisEquivNarrowClassGroupOverOriginal`: a group isomorphism `Gal(bigHilbertClassField K / K) ≃* RayClass.NarrowClassGroup K` sending the global norm-residue symbol of an idèle class `c` to the image under `bigHilbertClassFieldQuotientEquivNarrowClassGroup` of the coset of `c` modulo `bigHilbertClassFieldNormSubgroup`.
- Simp lemmas `..._globalNormResidue` and `..._idele`: on the norm-residue symbol of the class of an idèle `a`, the isomorphism gives the class of `a` modulo `RayClass.narrowDenominator`.

The norm range is computed by pushing both sides along the injective map `ideleClassCongr` of the base isomorphism `bigHilbertClassFieldBaseEquiv`: the image of the norm range over `K` is the norm range over the realized base (`ordinaryIdeleClassNorm_range_map_congrOfAlgEquiv`, using that the two algebra structures agree, `bigHilbertClassField_algebraMap_original`), which is the intrinsic subgroup by the realized-base result, and that subgroup is compatible with `ideleClassCongr`. The isomorphism is then `hilbertClassFieldGlobalReciprocityTransportData`.

## Points to watch

- The `K`-algebra structure on `bigHilbertClassField K` is the one from the imported file `BigHilbertClassFieldOverOriginalBase`.
- The isomorphism comes from the library's `globalReciprocityEquiv`; the file adds no reciprocity argument of its own.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/GlobalClassFields/HilbertClassFieldReciprocity/BigOriginal.lean`: the Lean file is the source byte for byte (SHA-256 `21f2c2f0df66f1eacbe453579d5a024ed46985d39aaf96c511bcd2bd9cee15d7`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
