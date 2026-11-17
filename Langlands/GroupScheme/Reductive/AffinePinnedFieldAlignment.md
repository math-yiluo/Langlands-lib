# Actual based coordinate root alignment on a field test

This internal construction takes two actual affine pinned models, a common
field algebra over their coefficient rings, an actual isomorphism of their
pullback groups and an actual isomorphism of their coordinate tori satisfying
the inclusion square. If the group isomorphism also preserves the canonical
Borels, `fieldBasedCoordinateIso` supplies a `BasedCoordinateIso` with exactly
those group and torus isomorphisms. It retains the full root-datum equivalence,
standard coordinate pairings, simple-root support correspondence and character
formula on every relative test. The field may be arbitrary, and the construction
works in every universe. No alignment of the chosen pinning vectors is claimed.

`fieldCoordinateEquiv` first uses `GeometricRootDatumComparison` on the actual
field realizations supplied by the models' fibrewise root data, then transports
through `CoordinateRootDatum.fieldRealizationEquiv`. Its weight map is pullback
by the prescribed torus isomorphism on the entire character lattice, including
central directions. The character equality also gives the all-test exponent
formula required by `BasedCoordinateIso`.

The positivity proof uses the actual canonical Borel, rather than choosing a
new torus map. `borelInclusionOver_represents` identifies its normalized
pullback inclusion with the dynamic parabolic of the canonical positive-coroot
cocharacter. A Borel square gives equality of these parabolics after transport.
The prescribed torus square expresses the transported source cocharacter in
the target torus. Applying `relativeRootSignInclusions` in both directions
identifies the signs of its pairings with all target roots. The full character
pullback formula and `pairing_root_positiveCorootSum` calculate these pairings
as twice the respective root heights. The published height criterion then
proves equivalence of positive roots.

Finally, `StarActionIndependence.mem_support_iff_of_isPos` recovers simple roots
from the positive sets for the two root data. Combining this with the actual
squares and the full character formula defines `fieldBasedCoordinateIso`.
This is an internal deduction from the named published constructions and
criteria, with no new original-literature assertion. It supplies field-test
alignment; extending that alignment to neighbourhoods, constructing correcting
torus sections and proving relative pinned comparison existence remain outside
this unit.
