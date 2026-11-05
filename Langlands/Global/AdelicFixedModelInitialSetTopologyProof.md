# Initial-set independence of actual arithmetic adelic point topologies

`Langlands.Global.adelicFixedModelInitialSetTopology` proves exactly
`Langlands.Global.AdelicFixedModelInitialSetTopologyStatement`. The two clauses
are proved by `curvePlaceFixedModelInitialSetTopology` and
`numberFieldFixedModelInitialSetTopology`.

## Scope and provenance

For an inclusion of finite sets S contained in U, the map is the existing
`curvePlaceFixedModelInitialSetEquiv` or `numberFieldFixedModelInitialSetEquiv`.
Its domain consists of actual full-adele points of an actual scheme over the
original outside-S integer ring. Its codomain consists of actual full-adele
points of that scheme's actual pullback to the outside-U integer ring. Both
sides have the independently defined arithmetic final topology. The original
scalar actions are retained.

This is the initial-set-enlargement comparison supporting Conrad, *Weil and
Grothendieck approaches to adelic points* (December 31, 2011), printed p.6 after
(3.5.1), with finite-stage topology and transitions as in Theorem 3.6, printed
pp.7–8. It is a derived comparison for a fixed model and its specified pullback.
It does not assert independence of two arbitrary spreads or identify the
model's full-adele points with adelic points of its generic fiber.

The theorem has exactly the target's finite-type hypotheses, expressed as
`LocallyOfFiniteType` and `QuasiCompact` of the structure morphism. It permits
nonaffine and nonseparated models and an empty S. The function-field clause
retains arbitrary constants and the stated rational-function presentation and
scalar tower. The number-field clause retains the full adelic ring, including
every infinite factor. The common universe remains arbitrary.

## Implemented proof

At every finite stage V containing U, the proof constructs a homeomorphism
between the original S-based stage and the U-based stage for the pulled-back
model. It composes three established homeomorphisms: the original S/V
fixed-model point homeomorphism, the inverse of the homeomorphism induced by
the canonical isomorphism between the iterated and direct model pullbacks,
and the inverse of the original U/V fixed-model point homeomorphism. The
pullbacks are compared by their actual isomorphism, without identifying them
by equality.

The inverse stage homeomorphism projects an actual scheme map to the original
model by `pullback.fst`. This follows from the first-projection law for the
canonical pullback-composition isomorphism and the inverse projection laws for
the two fixed-model point equivalences. Precomposing that identity with the
spectrum of the literal finite-level inclusion proves compatibility with the
full-adele comparison. Invertibility gives the forward compatibility as well.

Continuity of the forward full-adele equivalence follows from the universal
property `ringPointCoconeTopology_continuous_iff`. An arbitrary S-stage T first
maps to the stage indexed by T union U. This transition is continuous by
`adelicFixedModelTransitionTopology`. The cofinal-stage homeomorphism then
maps to a U-stage, which inserts continuously into its full-adele point space
by the definition of the target final topology. Cocone naturality and the
proved stage compatibility identify this composite with the restriction of
the actual full-adele equivalence.

For the inverse, every U-stage already has an S-stage with the same finite
set. Its inverse stage homeomorphism followed by insertion into the original
full-adele points is continuous. The inverse compatibility identifies that
composite with the inverse full-adele equivalence on the stage. Applying the
same final-topology universal property proves inverse continuity. A
homeomorphism with the original equivalence as its `toEquiv` gives the stated
`IsHomeomorph` conclusion. The proof repeats this argument for the full
number-field rings, without discarding archimedean coordinates.
