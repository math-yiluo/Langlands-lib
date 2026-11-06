# The ordinary isomorphism relation on full Tate-normalized Harris CM models

Author: Worker 344.

This internal construction works on the existing actual
`TateNormalizedCMRepresentative` values over the same connected admissible CM
base and geometric point, at the same original Harris level. Each representative
retains its actual abelian scheme, polarization, original rational algebra
action, supplied integral order action, original determinant and dimension
condition, original level orbit and full integral Tate normalization.

`tateNormalizedCM_integralActionRationalExtension` identifies the full rational
extension of each supplied integral action with its unchanged rational action.
The existing uniqueness theorem for extension from the full integral order
applies because the restriction agrees on every order element.
`tateNormalizedCMOrdinaryRationalIso` therefore constructs the original rational
action isomorphism from an actual abelian-scheme isomorphism intertwining only
the integral order actions. The published rational-extension intertwining
theorem extends this equation to every element of the full rational algebra.
Its forward and inverse rational arrows are exactly the rationalizations of the
actual arrows. A uniqueness theorem shows that any original rational action
isomorphism with this forward arrow equals the constructed isomorphism.

`tateNormalizedCMOrdinary_multiple_iff` identifies the geometric polarization
equation for that constructed rational isomorphism with exact integral
cross-multiple data for the actual forward arrow and the original scalar `q`.
It uses rationalization of the actual integral dual pullback and the existing
integral-multiple criterion. No denominator-square factor is introduced.

`TateNormalizedCMOrdinaryRelated` requires an actual abelian-scheme isomorphism,
exact equivariance for every element of the original integral order, the exact
integral polarization cross-multiple data with scalar `q`, and the original
level equation for the canonically induced rational isomorphism. A separate
rational action isomorphism is not a witness of this relation.

When the point field is algebraically closed and the Hodge image of the fixed
level preserves the original integral source span,
`tateNormalizedCMRelated_iff_ordinaryRelated` identifies this ordinary relation
with the unchanged normalized rational-isogeny relation. In the forward
direction the preceding integral-reflection construction supplies the actual
isomorphism and all its equations; uniqueness identifies the original rational
isomorphism with the induced one, retaining the exact level equation. In the
reverse direction the induced rational action isomorphism and the exact
polarization criterion give the original witnesses. The actual inverse is
equivariant by conjugating the forward equivariance equation with its inverse
identities. The final theorem combines the result with the existing criterion
for equality of the original CM classes.

The provenance is internal: these are consequences of the existing integral
order extension, rational action, integral dual-pullback and normalized
integral-isomorphism comparison constructions. Neither lattice realization nor
a representing scheme is an input. The comparison retains the source-stabilizer
hypothesis, the original scalar and original level orbit. It compares relations
on the same normalized representatives; it does not construct an independent
ordinary PEL parameter scheme or prove representability.
