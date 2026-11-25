# Norm subgroups of infinite extensions and the maximal unramified extension

Module `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.NormSubgroup`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

In the abstract class field theory of the library, a field is a closed subgroup of a topological group `G`, and a `G`-module `A` gives the invariants `A_K`. For a possibly infinite extension `E/K`, the norm group `N(E/K) A_E` is defined as the intersection of the norm images `N(M/K) A_M` over all finite intermediate fields `M`. The file sets up this subgroup and its quotient, and the maximal unramified extension `L̃` of `L` with the special case `N(L̃/K) A_L̃` used by the reciprocity map.

## Main definitions

- `FiniteIntermediateField E K`: a closed subgroup `G_M` with `G_E ≤ G_M ≤ G_K` and `G_K/G_M` finite. `FiniteIntermediateField.base` is `M = K`.
- `finiteIntermediateNormRange A E K M`: the image of the norm `A_M → A_K`.
- `infiniteNormSubgroup A E K`: the intersection of these images over all finite intermediate `M`, with `mem_infiniteNormSubgroup_iff`.
- `InfiniteNormQuotient A E K`: the quotient `A_K / N(E/K) A_E`, with the class map `infiniteNormClass`, the vanishing criterion `infiniteNormClass_eq_zero_iff`, surjectivity, an induction principle and the lift `infiniteNormQuotientLift`.
- `DegreeData.maximalUnramifiedField D L`: the closed subgroup `I_L = G_L ∩ ker d`, where `d` is the degree map of `D`. `mem_maximalUnramifiedField_iff` says `g ∈ I_L ↔ g ∈ G_L ∧ d(g) = 1`.
- `DegreeData.maximalUnramifiedNormSubgroup D A K L`: `infiniteNormSubgroup` for `E = L̃`. `MaximalUnramifiedNormQuotient` and `maximalUnramifiedNormClass` come with the same interface as the general quotient.

## Main results

- `maximalUnramifiedField_le`, `..._le_of_le`, `..._mono`: `I_L ≤ G_L`, `I_L ≤ G_K` when `G_L ≤ G_K`, and `I_L ≤ I_K` when `G_L ≤ G_K`.
- `extensionSubgroup_maximalUnramifiedField`: inside `G_K`, the subgroup of `L̃` is the relative inertia subgroup `extensionInertiaWithin K L`. By `extensionSubgroup_maximalUnramifiedField_normal` it is normal when `L/K` is normal.

## Watch for

- `N(E/K) A_E` is the library's own definition as an intersection over finite levels. It is not the norm from a single module, and it need not equal any single finite norm group.
- `L̃` is defined as the subgroup `G_L ∩ ker d` given by the degree map, not as a compositum of finite unramified extensions. In field terms, `maximalUnramifiedField_le` and `..._le_of_le` say only `L ⊆ L̃` and `K ⊆ L̃`.
- The quotients are plain definitions, which the file's comments describe as opaque. They are meant to be used through the class map, the induction principle and the lift, or through the explicit equivalences `infiniteNormQuotientConcreteEquiv` and `maximalUnramifiedNormQuotientInfiniteEquiv`, not by unfolding.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/NormSubgroup.lean`: the Lean file is the source byte for byte (SHA-256 `e4162dafd217cf66421a2dc6e85284b90069f8eea6d8686a86ed3d55272e42c8`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
