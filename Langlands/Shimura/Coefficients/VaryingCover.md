# Associated coefficient cospans for varying covers and groups

Author: Worker 13.

This is an internal construction from the actual equivariant diagrams and
associated small-etale sheaves. Let `X` be a scheme, `R` a commutative ring,
`D : I ⥤ GrpCat` a group diagram, and
`Y : EquivariantDiagram D X.Etale` a diagram of actual etale objects over
`X` with compatible actions. A coefficient input is
`M : EquivariantDiagram D (ModuleCat R)`. The scheme, coefficient ring,
coefficient module carriers, and groups use the same universe, as required by
the existing associated-sheaf construction. The index-object and index-morphism
universes are independent.

For an arrow `f : i ⟶ j`, write `φ = D.map f`. The cover transition is
`Y_i → res(φ) Y_j`, and the coefficient transition is
`M_i → res(φ) M_j`. These transitions have the same index direction, but
restriction of sections along a cover map is contravariant. The resulting
canonical sheaf maps therefore form the cospan

`Assoc(Y_i,M_i) → Assoc(Y_i,res(φ)M_j) ← Assoc(Y_j,M_j)`.

The left map is the existing associated-sheaf functor applied to the actual
coefficient transition. The right map is exactly `etaleCrossCoverMap` on
the actual cover transition and the identity restricted coefficient map.
The product pullback and inverse-deck conventions are inherited unchanged
from [EtaleCrossCover](EtaleCrossCover.md) and
[CrossCover](CrossCover.md).

`etaleAssociatedCoverChange` first makes the right map natural in a
single coefficient representation. Its naturality follows from the existing
`associatedCoverChange` naturality applied to the constant-sheaf action
of the coefficient morphism. `etaleAssociatedAt` evaluates an entire
coefficient diagram and applies the associated-sheaf functor.
`etaleAssociatedTransitionTarget` instead evaluates at `j`, restricts its
group action by `φ`, and uses the cover at `i`.

`etaleAssociatedReduction` and `etaleAssociatedComparison` are natural
transformations into that common target. Reduction naturality follows from
the underlying natural transformation in a morphism of equivariant diagrams,
then functoriality of the associated-sheaf construction. Comparison naturality
is obtained by whiskering `etaleAssociatedCoverChange`.

`etaleAssociatedTransitionCospan` packages both maps as a functor from
coefficient diagrams to actual `WalkingCospan` diagrams of sheaves.
It uses Mathlib's cospan in the functor category and then transposes the
two indexing categories. Thus its maps on coefficient morphisms, identity
law, and composition law come from those of the three sheaf functors and
the two natural transformations. The endpoint and leg theorems give the
displayed formulas as definitional equalities.

No finite-torsor assumption is needed to construct these cospans. The right
map is not asserted to be invertible here. When the input covers are finite
geometric torsors, proving invertibility of this exact map is the separate
`EtaleAssociatedCoverComparisonStatement` obligation. Reversing the right
leg and proving coherence across index arrows would then yield inverse
coefficient transitions. This file constructs the cospans for each arrow
and their functoriality in coefficient diagrams; it does not construct that
inverse system, actual Harris covers, a tensor comparison, or cohomology.

The provenance is the categorical combination of
[EquivariantDiagram](../../CategoryTheory/EquivariantDiagram.md) with the
published associated-sheaf and cross-cover constructions. No new result
is attributed to external literature.
