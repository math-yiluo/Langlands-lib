# Initial-set independence of actual arithmetic adelic point topologies

This derived target makes the initial-set comparison after equation (3.5.1)
in Brian Conrad, *Weil and Grothendieck approaches to adelic points*
(December 31, 2011), printed p.6, explicit for the arithmetic final topology.
Conrad states there that increasing the initial finite set has no impact on
the direct limit; Theorem 3.6 on p.6, with transition argument on p.8, supplies
the compatible arithmetic stage topologies.

Let `S ⊆ U` be finite sets of places, and let `X` be an arbitrary finite-type
scheme model over the original outside-`S` integer ring. Pull `X` back along
the literal integer inclusion to obtain its actual outside-`U` model. The
target asserts that `curvePlaceFixedModelInitialSetEquiv`, respectively
`numberFieldFixedModelInitialSetEquiv`, is a homeomorphism from full-adele
points of the original model to full-adele points of this actual pullback.
The equivalence was constructed using the pullback adjunction, with the
original scalar actions. Each topology is independently defined as final
from its own original arithmetic model stages; neither topology is defined
by transporting the other along this equivalence.

Finite type is expressed by `LocallyOfFiniteType X.hom` and
`QuasiCompact X.hom`. Separatedness and affineness are not assumed. The
function-field clause retains arbitrary constant fields with a compatible
finite extension of the rational-function field and its scalar tower. This
extension of Conrad's global-field setting uses only continuity of the
arithmetic transitions and canonical model-isomorphism comparisons, which
do not require finite residue fields. Every finite initial set, including
the empty set, is allowed. The number-field clause includes all infinite
factors of the full adele ring. The common universe is arbitrary.

A proof can compare cofinal stages containing `U`: direct base change to a
later set and successive base changes from `S` through `U` are canonically
isomorphic. These actual isomorphisms give homeomorphisms on stage points.
An original stage not containing `U` first maps continuously into its union
with `U`. Final-topology continuity in both directions then gives the target.
This is initial-set independence for a model and its specified pullback;
independence from two arbitrary spreads and generic-fiber identification
remain subsequent obligations. This file states a proposition and supplies
no proof of it.
