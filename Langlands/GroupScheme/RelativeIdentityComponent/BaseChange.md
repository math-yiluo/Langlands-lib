# Arbitrary base change of relative identity components

This file proves that a supplied relative identity-component representative
with geometrically connected fibres remains a representative after arbitrary
base change. It then derives `SmoothBaseChangeStatement` and the aggregate
`SmoothStructureStatement` from `SmoothExistenceStatement`. Every base scheme,
test scheme and residue field shares an arbitrary universe `u`. There are no
affineness, reducedness, separation or finiteness assumptions, and no
restriction on the base morphism.

## The actual pullback comparisons

The first declarations are in
`Langlands.GroupScheme.RelativeIdentityComponent`.

`overPullback_isPullback b f` identifies the underlying square of the actual
map `(Over.pullback b).map f` as a pullback of schemes. Its proof cancels the
right-hand defining pullback square from the outer defining pullback square.
`range_of_isPullback` expresses the range of the top arrow in a scheme
pullback as the inverse image of the range of the bottom arrow. It follows
from Mathlib's image/preimage theorem for actual scheme pullbacks, applied
to the whole source.

For `X : Over S` and `s' : S'`, `fiberComparison b X s'` is the actual
scheme map from the residue fibre of `X ×_S S'` at `s'` to the residue fibre
of `X` at `b(s')`. It is built with `pullback.map`, using the first
projection of `X ×_S S'` and the morphism induced by
`b.residueFieldMap s' : κ(b(s')) → κ(s')`.
`fiberComparison_isPullback` proves that this fibre comparison is a base
change along that spectrum morphism. `fiberComparison_naturality` proves
commutativity for every `f : X → Y` over `S` by checking the two pullback
projections.

`fiberMap_isPullback` proves that the square formed by these two comparisons
and the residue-fibre maps induced by `f` is cartesian. It cancels the
cartesian comparison square for `Y` from the comparison square for `X`,
using naturality and the equations saying that the fibre maps are over their
respective residue fields. These maps concern actual iterated pullbacks; no
identification of those objects by definitional equality is assumed.

## Images and the all-test representation predicate

The next declarations are in
`Langlands.GroupScheme.IsRelativeIdentityComponent`.

`range_eq_underlyingSet hi` proves that a supplied representative inclusion
has image exactly `RelativeIdentityComponent.underlyingSet G`. One inclusion
uses the representative's factorization criterion on its own source.
For the reverse inclusion, the canonical map from the spectrum of a total
space point's residue field has singleton image in the relative identity set.
The all-test criterion factors this map through the representative, providing
a preimage of the original point.

`range_residueFiber hi s` applies the pullback image formula and the exact
fibre membership theorem for `underlyingSet`. Thus the inclusion pulled back
to `κ(s)` has image exactly the identity connected component of that fibre.
`isClosedImmersion_residueFiber hi s` then proves that this fibre inclusion
is a closed immersion: it is already an open immersion, hence a preimmersion,
and its image is the closed connected component. The inclusion in the total
space is not asserted to be closed.

The converse helpers reconstruct the representation predicate from images.
`range_eq_underlyingSet_of_residueFiber` uses the pullback image formula and
the lift of each point to its own residue fibre to recover the total-space
image from the exact fibre images.
`of_range_eq_underlyingSet` assumes an open inclusion with that total image.
Factoring a test morphism through the open immersion is equivalent to its
whole image lying in that image. The underlying-set range criterion identifies
this with the published residue-fibre condition.
`of_range_residueFiber` combines these two helpers. These factorization
statements quantify over all test schemes, including nonaffine and nonreduced
ones.

## Arbitrary base change and the conditional structure theorem

`IsRelativeIdentityComponent.baseChange hi b` assumes
`GeometricallyConnected H.X.hom` for the source of the representative
`i : H → G`. The base-changed inclusion is open. On each residue fibre over
the new base, `fiberMap_isPullback` exhibits its inclusion as a pullback of
an original closed fibre inclusion, so it is also closed. Its source is
connected by geometric connectedness and stability under base change.
The existing unrestricted characterization
`IdentityComponent.range_eq_identitySet` therefore identifies its range
with the new identity component: the connected image contains the identity,
and the open and closed image contains the whole identity component.
`of_range_residueFiber` gives the exact all-test representation predicate
over the new base.

The last declarations are in
`Langlands.GroupScheme.RelativeIdentityComponent`.
`smoothBaseChange_of_existence` obtains a geometrically connected
representative from the smooth-existence premise, transfers geometric
connectedness to any supplied representative with the compatible comparison
from `RelativeIdentityComponentProperties`, and applies the base-change
theorem. `smoothStructure_of_existence` combines this result with
`smoothNormality_of_existence` and the same existence premise.

## Provenance and remaining scope

These are derived internal results using the already specified all-test
predicate, the underlying-set range criterion, Mathlib's actual pullback and
residue-fibre geometry, and the existing characterization of a connected
open and closed subgroup over a field. Although the source file of that last
characterization also constructs smooth affine field components, the
characterization itself explicitly omits smoothness and affineness; neither
is used here. No new external source assertion is introduced.

Smooth existence remains a premise of the two conditional smooth theorems.
This unit does not prove `SmoothExistenceStatement` and does not alone prove
the published `SmoothStructureStatement` without premises. It leaves the
existence obligation of the enclosing task intact.
