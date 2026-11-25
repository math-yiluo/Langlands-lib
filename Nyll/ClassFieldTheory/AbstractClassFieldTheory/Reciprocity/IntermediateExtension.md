# Intermediate fields of a finite Galois extension

Module `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.IntermediateExtension`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `G` be a topological group and `L/K` a finite Galois extension of abstract fields, given by a closed normal subgroup `G_L ≤ G_K` of finite index. A subgroup `S ≤ G(L/K)` has an inverse image in `G_K`. This file realizes that inverse image as a closed intermediate field `M = L^S` and proves the two Galois group identifications `G(L/M) ≅ S` and, for normal `S`, `G(L/K)/S ≅ G(M/K)`. This is the direction of the Galois correspondence used in the reductions of the abstract reciprocity proof.

## Definitions

- `intermediateSubgroup L S`: the inverse image of `S` in `G_K`. It contains `G_L`.
- `intermediateField L S`: the same subgroup as a closed subgroup of `G`, lying between `G_L` and `G_K` (`intermediateField_le_base`, `field_le_intermediateField`).
- `intermediateCoset L q`: the fiber of `G_K → G(L/K)` over `q`.
- `lowerFiniteGalois L S`: `L/M` as a finite Galois extension.
- `intermediateFiniteGalois L S hS`: `M/K` as a finite Galois extension, for normal `S`.
- `intermediateFiniteAbstractExtension`: `M/K` as a finite extension, without normality.
- `lowerRestrictionHom`: the map `G_M → S`. It is surjective, with kernel `G_L`.
- `upperQuotient L S`: the quotient `G(L/K)/S`.

## Results

- `intermediateSubgroup_isClosed`: the inverse image is closed. It is a finite union of cosets of `G_L` (`intermediateSubgroup_eq_iUnion_cosets`), each closed as a translate of a closed subgroup.
- `extensionSubgroup_intermediateField_eq`: pulling `M` back to `G_K` recovers `intermediateSubgroup L S`.
- `intermediateField_finite` and `extension_over_intermediate_finite`: `M/K` and `L/M` are finite. `extensionSubgroup_over_intermediate_normal`: `L/M` is normal.
- `intermediateField_normal`: `M/K` is normal when `S` is.
- `lowerQuotientEquiv`: `G(L/M) ≃* S`, from the first isomorphism theorem applied to `lowerRestrictionHom`.
- `upperQuotientEquiv`: `G(L/K)/S ≃* G(M/K)` for normal `S`, from the third isomorphism theorem.
- `intermediateSubgroup_map_quotient_eq`: the image of the inverse image of `S` is `S`.

## Watch for

- Only the passage from subgroups of `G(L/K)` to intermediate fields is constructed here. Bijectivity of the Galois correspondence is not stated in this file.
- Fields are represented contravariantly by closed subgroups, so "`L ≤ M`" in the names means `G_L ≤ G_M`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/IntermediateExtension.lean`: the Lean file is the source byte for byte (SHA-256 `d99abf851b14b7aa1f6c16866a10f3ca23188b0bd0fc4c037b26bda7697c857b`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
