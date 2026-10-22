# Subgroup tower coordinates on actual Tate cohomology

Author: Worker 45.

Let `K ≤ H` be subgroups of a group `G`. The existing Mathlib equivalence
`(Subgroup.subgroupOfEquivOfLe h).symm` is the canonical group isomorphism
`K ≃* K.subgroupOf H` sending `k` to `k` viewed as an element of `H`;
both directions are the identity on underlying elements of `G`.

For a representation `A` of `G`, `towerCoefficientIso h A` is the identity of
the underlying module of `A`, viewed as an isomorphism between two ways of
restricting `A` to the same group: first to `K` and then along
`Subgroup.subgroupOfEquivOfLe h`, or first to `H` and then to `K.subgroupOf H`.
`towerSequenceMap h S` applies this identification to all three terms of a
short complex `S` of representations of `G`.

For finite groups, `towerReindex h A n` is the isomorphism
`Ĥⁿ(K, A) ≅ Ĥⁿ(K.subgroupOf H, A|_H)` of Mathlib's actual Tate cohomology
groups, in every integer degree `n`. It is the map `reindexIso` of
`Reindex` for the group isomorphism `(Subgroup.subgroupOfEquivOfLe h).symm` and the
coefficient isomorphism `towerCoefficientIso h A`, hence it is induced by
an isomorphism of actual Tate complexes.

This file only fixes the coordinates. It is needed to state transitivity of
restriction and corestriction for a tower `K ≤ H ≤ G`, because the
restriction of `A` to `K` through `H` lives over the group
`K.subgroupOf H`, not over `K`. No transitivity law is claimed here.

This is an internal coordinate construction with no counterpart in the
literature, which regards `K` as a subgroup of `H` without change of
notation. Restriction is the change-of-group map along a subgroup inclusion
in Serre, *Local Fields* (1979), Chapter VII, section 5, printed
pp. 115–116 (PDF pp. 121–122), and corestriction is defined in Chapter VII,
section 7, printed pp. 118–119 (PDF pp. 124–125). Source `serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
