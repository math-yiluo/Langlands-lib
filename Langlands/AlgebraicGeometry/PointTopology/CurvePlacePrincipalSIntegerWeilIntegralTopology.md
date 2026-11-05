# Integral Weil points of actual curve S-integer models

This derived construction proves the integral local homeomorphism used in
Conrad, *Weil and Grothendieck approaches to adelic points* (2011), Example 4.2,
printed page 10. Here the scheme is over the actual upper global S-integer
ring, with the full exceptional-place preimage. The lower exceptional sets are
the cofinal principal sets proved in `CurvePlacePrincipalSInteger`.

For an original lower place v outside this exceptional set, and an upper
S-integer scheme Y with an actual relative projective immersion,
`curvePlacePrincipalSIntegerWeilRestrictionPointHomeomorph` constructs a
homeomorphism from the lower completed-integer points of the actual relative
Weil restriction to the product of Y's original upper completed-integer points
over every upper place above v.

Each point topology is the existing `schemePointTopology`. The product has
the product of these topologies; no topology is defined by transport through
the claimed comparison. The relative Weil scheme is the existing
`affineChartWeilRestriction`, whose construction glues the actual affine Weil
charts. The relative projective immersion supplies separatedness and finite
affine neighborhoods, so nonaffine Y is included.

The actual upper S-integer ring is already proved finite projective over the
actual lower ring. `CurvePlacePrincipalSIntegerLocalTensor` supplies the actual
completed-integer coefficient decomposition and identifies its right tensor
factor with each original upper coefficient inclusion. The original completed
upper integer rings are finite projective modules over the completed lower
integer ring, and their inherited topologies have the finite-module topology
by `CurvePlaceIntegralTopology`. Applying the proved general
projective-immersion completed-tensor Weil point homeomorphism therefore gives
the displayed comparison.

The counit identity proves that each upper component is the original relative
Weil counit evaluated along the actual completed-integer factor test spectrum.
It follows directly from the general counit identity with the same arithmetic
instances and tensor comparison. Thus the construction retains the original
point map, in addition to proving a topological equivalence.

The lower field is a function field over finite constants, finite over the
specified parameter subfield, and the original upper extension is finite.
The compatible constant-field structures are explicit. The chart denominator
is nonzero, and v lies outside the stated exceptional set. All fields inhabit
an arbitrary common universe; no separability is required. Y is locally of
finite type and has the specified relative projective immersion. The result
does not claim that every Y admits such an immersion. The actual model
existence is proved separately; the finite-level adelic product and full
adelic Weil comparison remain obligations of the host task.
