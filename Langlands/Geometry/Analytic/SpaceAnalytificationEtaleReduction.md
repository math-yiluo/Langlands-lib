# Conditional reduction of the algebraic-space étale comparison

This supporting module develops the final assembly for
`SpaceAnalytificationEtaleStatement`. It does not prove that statement:
localized source descent and reflection of étaleness on affine test points
are explicit hypotheses.

`pointHom_map` is the inverse Yoneda equivalence's composition law for
`RingPoints.map`. `EtaleAffineTest` retains each test algebra, its ring and
algebra structures, a finite polynomial presentation, a point, and its
algebraic étaleness proof. Its universe is `u + 1`; the analytic spaces
remain in `LocalizedCategory.{u,u,u}`.

`etale_of_isEtaleMorphism_of_sourceDescent` uses precisely this family.
The source analytification supplies its étaleness and joint surjectivity.
Compatibility with `F` identifies its composites with maps attached to
étale points of the target space. The target analytification makes these
composites étale. The assumed source-descent proposition gives étaleness
of `F`. This direction needs no separatedness or local finite-type
hypothesis.

For the converse, the module assumes that an étale map `p A P x` has an
étale represented point `pointHom K x`. For a finite-type affine étale
test of the source, composition gives an étale map into the target
analytification, and compatibility identifies it with the map attached
to the composite algebraic point. The assumed reflection property and
`isEtaleMorphism_iff_finiteTypeAffineTests` then imply that `f` is étale.
`FinitePolynomialPresentation.ofFiniteType` supplies the presentation for
each finite-type algebra. Only the source's local finite-type condition
is needed by this conditional argument.

The provenance is internal and derived: the argument assembles the
published definitions of `IsAnalytification`, `IsEtaleMorphism`, and
localized étaleness using Yoneda naturality, the included algebraic
affine-test reduction, and two stated analytic inputs. Neither of these
inputs is supplied by this module. The companion module
`SpaceAnalytificationEtaleReflection` constructs affine-point reflection
from actual affine pullbacks, localized étale base change, and reflection
for actual affine algebra maps. The source-descent type is expanded in
the theorem hypotheses, so this module does not depend on a separate
unproved source-descent declaration.

`pointHom_changeRing` identifies change of test algebra on a ring point with precomposition of its represented point by the induced test morphism.
