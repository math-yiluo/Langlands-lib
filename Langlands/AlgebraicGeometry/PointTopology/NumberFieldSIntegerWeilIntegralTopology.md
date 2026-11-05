# Integral Weil points of actual number-field S-integer models

This derived construction proves the integral local homeomorphism used in
Conrad, *Weil and Grothendieck approaches to adelic points* (2011), Example 4.2,
printed page 10. Here the scheme is over the actual upper global S-integer
ring, with the full exceptional-place preimage. The lower exceptional set S is
any finite set of original finite places.

For an original lower place v outside this exceptional set, and an upper
S-integer scheme Y with an actual relative projective immersion,
`numberFieldSIntegerWeilRestrictionPointHomeomorph` constructs a
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
actual lower ring. `NumberFieldSIntegerLocalTensor` supplies the actual
completed-integer coefficient decomposition and identifies its right tensor
factor with each original upper coefficient inclusion. The original completed
upper integer rings are finite projective modules over the completed lower
integer ring, and their inherited topologies have the finite-module topology
by `AdelicFunctoriality.IntegralTopology`. Applying the proved general
projective-immersion completed-tensor Weil point homeomorphism therefore gives
the displayed comparison.

The counit identity proves that each upper component is the original relative
Weil counit evaluated along the actual completed-integer factor test spectrum.
It follows directly from the general counit identity with the same arithmetic
instances and tensor comparison. Thus the construction retains the original
point map, in addition to proving a topological equivalence.

K and L are original number fields in an arbitrary common universe, with the
given field embedding. The `Fact` premise states that v lies outside S. An empty
finite-place S is allowed. Y is locally of finite type and has the specified
relative projective immersion. The result does not claim that every Y admits
such an immersion. Actual model existence is proved separately; the finite-level
adelic product and full adelic Weil comparison remain obligations of the host task.
