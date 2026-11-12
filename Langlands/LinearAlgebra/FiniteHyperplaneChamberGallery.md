# Finite galleries of rational sign chambers

This internal linear algebra construction for Task 5515 concerns a finite
family of rational linear forms on an arbitrary rational vector space.
It composes the generic segment construction in `FiniteHyperplaneSegment`
with the interval subdivision in `FiniteHyperplaneGallery`. No finite
dimensionality, nonempty family, or root-system structure is assumed.

`crossingTime f x y` is `f(x)/(f(x)-f(y))`. If `f(x)` is nonzero, a zero
of `f` along the segment from `x` to `y` must occur at this parameter.
Conversely, this parameter is a zero whenever the denominator is nonzero.
`crossingTimes` is the finite image of these parameters, restricted to the
open unit interval. Every member has a form vanishing there. When both
endpoints are regular, parameters in the closed unit interval outside this
finite set give regular vectors.

`WallAdjacent f keep x y` requires regular endpoints and an actual rational
vector `w` on at least one wall. Every form vanishing at `w` has opposite
strict signs at the endpoints. Every form nonzero at `w` has the same strict
sign at `x`, `y` and `w`. Any two vanishing forms are proportional by a
nonzero rational scalar. Finally, every index satisfying the predicate
`keep` has nonzero evaluation at `w`. `ChamberStep` is the disjunction of
strict sign agreement for all forms and this wall adjacency.

The affine auxiliary lemmas are proved directly over the rationals.
Opposite endpoint signs give an interior zero by division by the nonzero
slope. Conversely, an interior zero gives opposite endpoint signs by
factoring the two values as the slope times their distances from the zero.
Thus an interval without zeros preserves strict signs.

On an interval with regular endpoints and at most one crossing parameter,
there are two cases. If there is no crossing, all signs agree. Otherwise
choose the unique crossing parameter. Off that parameter every segment
vector is regular. The affine lemmas then show that vanishing forms reverse
sign, and that all other forms keep their sign at both endpoints and the
wall vector. Simultaneous-crossing proportionality supplies the required
wall class. Forms with matching signs at the original endpoints cannot
vanish anywhere on the closed segment, so their walls are avoided.

`reflTransGen_chamberStep_of_generic` applies finite sparse subdivision to
these local steps and maps the resulting parameter chain to segment
vectors. The final theorem `reflTransGen_chamberStep` joins any two regular
vectors by the reflexive transitive closure of `ChamberStep`, provided the
forms selected by `keep` have matching strict endpoint signs. It first
chooses a generic endpoint in the second endpoint's chamber, uses the
segment chain to that endpoint, and appends the same-chamber step to the
specified endpoint.

The provenance is the elementary finite-hyperplane argument implemented
above, using the two imported internal helpers. This module proves only
the rational sign-chamber gallery. Realizing its vectors and walls by
actual dynamic parabolics, proving maximality of the inner parabolics,
and the representation-theoretic application remain separate obligations.
