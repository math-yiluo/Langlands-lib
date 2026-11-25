# The big Hilbert class field as an extension of the original field

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.BigHilbertClassFieldOverOriginalBase`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The library builds the big (narrow) Hilbert class field `bigHilbertClassField K` over a fixed-field copy `bigHilbertClassFieldBase K` of the number field `K`, not over `K` itself. This file makes it a `K`-algebra through the canonical isomorphism `bigHilbertClassFieldBaseEquiv : K ≃ bigHilbertClassFieldBase K`, and transfers its properties to `K`.

## Main definitions and results

- `bigHilbertClassFieldBaseAlgebraOverOriginal`, `bigHilbertClassFieldAlgebraOverOriginal`: the algebra structures over `K`; by `bigHilbertClassField_algebraMap_original`, the scalar map is the base isomorphism followed by inclusion of the fixed field. `bigHilbertClassFieldScalarTowerOverOriginal` gives the scalar tower.
- `bigHilbertClassFieldBaseEquivOverOriginal`: `K ≃ₐ[K] bigHilbertClassFieldBase K`; the base has degree `1` over `K` (`bigHilbertClassFieldBase_finrank_over_original`).
- `bigHilbertClassFieldFiniteDimensionalOverOriginal`, `bigHilbertClassFieldIsGaloisOverOriginal`, `bigHilbertClassFieldIsAbelianGaloisOverOriginal`: the field is finite, Galois and abelian over `K`.
- `bigHilbertClassField_finrank_over_original_eq_narrowClassGroup_card`: `[bigHilbertClassField K : K]` is the order of the narrow class group. The degree is the index of the big-Hilbert norm subgroup, by the imported degree formula for closed finite-index class fields, and the quotient is the narrow class group.

These are global instances, so `K`-algebra statements about `bigHilbertClassField K` elsewhere use this scalar map.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/GlobalClassFields/BigHilbertClassFieldOverOriginalBase.lean`: the Lean file is the source byte for byte (SHA-256 `aa36cbb01c912cfd3b123a7de70fb3fa10a10a4513aee71e89cd41eb7fe2ef1b`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
