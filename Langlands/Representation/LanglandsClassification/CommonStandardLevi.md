# Common actual standard Levi groups

This internal construction supports the common-group formulation of Renard
VII.4.2(ii). It starts with two compatible root presentations relative to the
same torus inclusion and generic cocharacter, and **assumes equality of their
simple-root indices**. No parameter-injectivity theorem is proved here.

`ParabolicRootPresentationData.IsCompatible.levi_range_eq_of_index_eq` identifies
the two actual ambient Levi images as subgroup functors on every test scheme:
both equal the standard Levi for the shared index. `commonLeviIso` applies the
published inclusion-compatible isomorphism of closed subgroup representatives.
Its forward and inverse maps commute with the original ambient inclusions,
and the forward compatibility uniquely determines the forward map. The Levi
schemes may have different carriers and different intermediate parabolic
schemes.

For any two actual rational Levis with equal literal images in the ambient
rational-point group, `commonLeviPointsEquiv` identifies their rational points
as topological groups. It uses each published `leviPointsEquiv` and the
topological equivalence between equal subgroups. Each point group carries its
own canonical topology; only a topological ground field and affine ambient
group are required. The ambient compatibility theorem and
`commonLeviPointsEquiv_eq_iff` show that this comparison pairs exactly those
points with equal images under the two original ambient maps.

The two subsequent equivalences express the comparison conditions in the
published injectivity conclusion using this single group:

- `commonLeviPoints_norm_iff` rewrites equality of complex-character norms on
  common ambient points as equality after precomposing the second character
  with the comparison.
- `commonLeviPoints_intertwines_iff` does the same for any complex linear map
  between representations, with independent carrier universes.
- `commonLeviRepresentationEquiv` packages an invertible such map as an actual
  representation equivalence. `exists_commonLeviRepresentationEquiv_iff`
  proves equivalence of its existence with the original all-pairs
  linear-equivalence condition.

Finally, `commonStandardLevi_pointImage_eq` supplies the needed image equality
from the two compatible presentations and equal indices.
`commonStandardLeviPointsEquiv` is the resulting topological comparison.
`commonStandardLeviPointsEquiv_eq_map` identifies it with the rational-point
map of `commonLeviIso`, so the scheme and topological constructions agree.

The proof uses equality of represented all-test images, uniqueness of closed
subgroup representatives, and the already published canonical topology
comparisons. The norm and action rewrites use the proved characterization of
corresponding points. These are derived internal adapters, rather than new
assertions attributed to the literature. Their intended application is
Renard, *Représentations des groupes réductifs p-adiques*, 2026 version,
VII.4.2(ii), printed pp.243–246 / PDF pp.249–252.

The equality of the indices, the spectral norm equality and the existence of
the equivariant linear equivalence remain mathematical obligations in the
classification proof. This module proves neither those assertions nor
exhaustion, and it leaves the published classification statement and its
imports unchanged.
