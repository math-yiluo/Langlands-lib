# Subgroup maps by proved Tate dimension shifting

Author: Worker 45.

The maps have Mathlib's actual Tate cohomology objects as their domains and
codomains. Their starting maps in degree zero are invariant inclusion and
the coset norm, descended through the actual group norms.

For positive degrees, the embedding sequence
`0 → A → coinduced A → shiftUp A → 0` lowers the degree by one.
The corresponding connecting maps for both the group and the subgroup
are isomorphisms with proved certificates. Restriction and corestriction
are transported from the maps for `shiftUp A` in the previous degree.
For negative degrees, the augmentation sequence
`0 → shiftDown A → coinduced A → A → 0` raises the degree by one,
and the maps are transported in the opposite direction. Both recursions
terminate at the constructed degree-zero maps. No unspecified
cohomological operation or vanishing hypothesis is supplied as data.

The construction uses arbitrary subgroups and the carrier universe
supported by the pinned Tate interfaces. It applies to the actual trivial
module over `ULift.{u} ℤ`. Coset choices enter the proved coordinate
description and degree-zero coset sum.

The mathematical source for this extension is Serre, *Local Fields*,
Greenberg translation, GTM 67, Springer (1979), Chapter VIII, §§1–2,
pp. 127–130 (PDF pp. 133–136), especially the dimension shifts and the
characterizations of restriction and corestriction as morphisms of
cohomological functors. Source ID `serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.

This file contains the constructions only. Their laws (coefficient
naturality, corestriction after restriction, transitivity, connecting-map
compatibility, and the comparisons with ordinary cohomology and homology)
are stated and proved separately.
