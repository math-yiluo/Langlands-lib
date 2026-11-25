# The infinite abelian class field correspondence

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.InfiniteAbelianClassFieldCorrespondence`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a number field `K`, the file builds the order-reversing bijection between closed subgroups of `ideleClassComponentQuotient K`, the idèle class group modulo its identity component, and intermediate fields of `maximalAbelianExtension K`. It composes the imported reciprocity isomorphism of topological groups `ideleClassComponentQuotientEquivMaximalAbelianGalois K` onto `Gal(maximalAbelianExtension K / K)` with Mathlib's infinite Galois correspondence, then identifies the finite layers with norm subgroups.

## Main definitions and results

- In `ClosedSubgroup`: `mapContinuousMulEquiv` transports a closed subgroup along a topological group isomorphism; `orderIsoMapContinuousMulEquiv` and `orderDualIsoMapContinuousMulEquiv` are the induced order isomorphisms; `coe_mapContinuousMulEquiv` says the carrier is the image set.
- `infiniteAbelianClassFieldCorrespondence K : (ClosedSubgroup (ideleClassComponentQuotient K))ᵒᵈ ≃o IntermediateField K (maximalAbelianExtension K)`. A subgroup goes to the fixed field of its transport (`_apply`), a field to its fixing subgroup transported back (`_symm_apply`), and the fixing subgroup of the field attached to `H` is the transport of `H` (`_fixingSubgroup`).
- `infiniteAbelianClassFieldCorrespondence_finite_iff_open`: the field attached to `H` is finite over `K` if and only if `H` is open.
- `maximalAbelianGlobalArtin_comap_fixingSubgroup`: for a finite Galois intermediate field `E`, the preimage of `Gal(K^ab / E)` under the maximal abelian Artin map `maximalAbelianGlobalArtin K` is the norm range of `ideleClassNorm K E`.
- `infiniteAbelianClassFieldCorrespondence_comap_fixingSubgroup`: the preimage under the Artin map of the fixing subgroup of the field attached to `H` is the preimage of `H` in the idèle class group.
- `infiniteAbelianClassFieldCorrespondence_eq_finiteLayer_iff`: the field attached to `H` equals a finite Galois intermediate field `E` exactly when the preimage of `H` in the idèle class group is the norm range of `E`.
- `infiniteAbelianClassFieldCorrespondence_eq_closedFiniteIndexClassField`: if the preimage `P` of `H` has finite index, the field attached to `H` is the library's selected class field `closedFiniteIndexClassField P`, placed in the maximal abelian extension by `finiteAbelianExtensionInMaximalAbelianExtension`.

Finiteness against openness follows from Mathlib's `InfiniteGalois.isOpen_iff_finite` and the transport being a homeomorphism. The finite-layer results use that the maximal abelian Artin map projects to the finite Artin map of `E`, whose kernel is the norm range, and, for the converse, that the maximal abelian Artin map is surjective.

## Points to watch

- The correspondence is on closed subgroups of the component quotient, not of the idèle class group itself; `H` enters the statements on the idèle class group through its preimage. The domain is order-dual: larger subgroups give smaller fields.
- The maximal abelian extension, the reciprocity isomorphism, its Artin map and the selected finite class fields are the library's own constructions, imported here; the file adds the order-theoretic transport and the finite-layer identifications.
- The comparison with selected class fields is stated only for `H` whose preimage has finite index (passed as an instance).
- The finite-layer results are equalities of intermediate fields, not just isomorphisms.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/GlobalClassFields/InfiniteAbelianClassFieldCorrespondence.lean`: the Lean file is the source byte for byte (SHA-256 `64a3c43023b0b90648358b78f1b2227ec6ef5c03b419b4bbabf747792a985358`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
