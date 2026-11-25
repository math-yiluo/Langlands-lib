# The infinite part of the conductor and the full conductor

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ConductorInfinitePart`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

A modulus of a number field K (`RayClass.Modulus K`) has a finite part and an infinite part, a finite set of real places at which positivity is imposed. This file treats the archimedean part of the conductor of a subgroup H of the idèle class group C_K. The positivity condition at a real place v can be dropped from a defining modulus exactly when the image of K_vˣ in C_K already lies in H. With this, the file assembles the full conductor and proves that it is the least defining modulus.

## Main definitions and results

- `eraseRealPlace_isDefiningModulus_iff`: erasing a real place v from m gives a defining modulus for H if and only if m is defining and the one-place image `(IdeleGroup.infinitePlaceIdeleClass v).range` lies in H. `eraseRealPlaces_isDefiningModulus_of_ranges_le` erases a finite set of such places.
- `infinitePlaceIdeleClass_range_le_congruenceSubgroup_of_not_mem`: if v is not in the infinite part of m, the whole one-place image at v lies in the ray congruence subgroup of m.
- `ConductorialSubgroup.fullConductorInfinitePart H`: the real places whose one-place image is not contained in H. Every defining modulus contains them.
- `ConductorialSubgroup.fullConductor H`: the modulus with finite part the narrow finite conductor of H and this infinite part.
- `fullConductor_isDefiningModulus` and `isDefiningModulus_iff_fullConductor_le`: the full conductor is defining, and a modulus is defining exactly when it is at least the full conductor.

## Proof

For the hard direction of the erasure criterion, an idèle a in the congruence subgroup of the erased modulus is split as a = b · s. Here s is the idèle concentrated at v with the v-component of a, and b lies in the congruence subgroup of m. That the full conductor is defining uses the imported existence of a defining modulus whose finite part is exactly the narrow finite conductor (`exists_definingModulus_finitePart_eq_narrowFiniteConductor`). The real places outside the full infinite part are then erased from it.

## Points to watch

The erasure criteria hold for an arbitrary subgroup H. The full conductor and its infinite part are defined only for H of type `ConductorialSubgroup K`, the library's notion of a subgroup that has at least one defining modulus.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/GlobalClassFields/ConductorInfinitePart.lean`: the Lean file is the source byte for byte (SHA-256 `8cdfbaeebd4a774e2b7c86b31ca1a3fa1b2f2e136c3758ab9022ca8aa426d179`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
