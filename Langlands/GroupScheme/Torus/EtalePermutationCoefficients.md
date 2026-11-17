# Coefficient equivalences on permutation-atlas overlaps

This internal adapter relates normalized atlas coordinates to coordinates of
the original group scheme on the same test. It is derived from the published
base-change point equivalence, the split-torus point model and pullback
comparison.

`chartPointsEquiv f e t` identifies original group points over `t ≫ f` with
unit families on the test `T`, using the split chart `e` over `f`.
`coordinates` presents this evaluation using the underlying scheme morphism
and its compatibility equation. `coordinates_congr` records independence
under equality of the test and group morphisms.

`restrictChart_coordinates` states that the normalized restriction
`restrictChart f e q r h` evaluates the original chart at `T.hom ≫ q` on
the projection of the given pulled-back group point to the original group.
Its proof checks that the pullback comparison preserves the projection,
then uses naturality of the base-change point equivalence and the defining
point formula of the split-torus base-change isomorphism.


`AgreeBy.coordinates` turns an all-test equation for normalized charts into
an equation on a morphism to the original group scheme. It constructs the
corresponding point of the direct pullback using `baseChangePointsEquiv`
and its inverse law.

`transitionUnits` is one function from source unit families to target unit
families on every test over a common base. It inverts the original source
chart, keeps the underlying morphism to the original group, and evaluates
the original target chart. The equality of the two base composites makes
this evaluation well defined.

`transitionUnits_eq_on_open` proves that any `AgreeBy` permutation on an
open gives the local formula for this same function on every relative
test whose range is in that open. The test lifts through the open
immersion. The lift equation identifies both original-chart evaluations,
and the inverse law for the source chart recovers the given unit family.

`LocallyPermutes.coefficientDatum` chooses the opens and permutations from
`LocallyPermutes`. The point-indexed opens cover the overlap. The preceding
local formula allows `LocalCoefficientReindexing.ofUnitTransform` to derive
agreement of the chosen permutations on every nonempty intersection.
There is no assumption that a disconnected overlap has one permutation.

`LocallyPermutes.coefficientEquiv` is consequently an actual algebra
equivalence from `I`-indexed to `J`-indexed families of global sections on
`pullback f g`, over that overlap's global-section ring. Its local formula
is `LocalCoefficientReindexing.Datum.equiv_restrict` applied to
`coefficientDatum`. Empty overlaps and empty finite coordinate types are
allowed.

This derived unit uses the actual split-torus and group-scheme pullback
point models, the internal `EtalePermutationAtlas` interface, open
immersion lifting, and structure-sheaf coefficient gluing. It does not
construct a descent coaction, prove a cocycle for these algebra maps, or
establish effective descent or the Weil presentation statement. Those
remain separate obligations in the surrounding proof.
