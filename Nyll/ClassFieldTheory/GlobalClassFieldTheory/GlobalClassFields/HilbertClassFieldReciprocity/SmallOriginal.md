# Reciprocity for the small Hilbert class field over the original field

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.HilbertClassFieldReciprocity.SmallOriginal`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The file states global reciprocity for the selected small Hilbert class field `smallHilbertClassField K` of a number field `K`, regarded as an extension of `K` itself rather than of its realized base field.

- `smallHilbertClassField_ideleClassNorm_range_over_original`: over `K`, the image of the idèle-class norm is `smallHilbertClassFieldNormSubgroup (K := K)`.
- `smallHilbertClassFieldGaloisEquivClassGroupOverOriginal` (with the bundled `...ReciprocityOverOriginalData`): an isomorphism `Gal(smallHilbertClassField K / K) ≃* ClassGroup (𝓞 K)` sending the global norm-residue symbol of an idèle class `c` to the image under `smallHilbertClassFieldQuotientEquivClassGroup` of its coset modulo `smallHilbertClassFieldNormSubgroup`; on the class of an idèle `a` it gives `IdeleGroup.idealClass a` (simp lemmas).

The norm range is transported along the injective `ideleClassCongr` of the base isomorphism, reducing to the realized-base result of `HilbertClassFieldReciprocity.SmallActual`; the isomorphism is `hilbertClassFieldGlobalReciprocityTransportData`.

The `K`-algebra structure comes from the imported file `SmallHilbertClassFieldOverOriginalBase`, and the isomorphism from the library's `globalReciprocityEquiv`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/GlobalClassFields/HilbertClassFieldReciprocity/SmallOriginal.lean`: the Lean file is the source byte for byte (SHA-256 `f96d86a1accca6f8405dcc1f5b70593efff88b7309e0e7e245fff424d745e2a9`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
