# Pullback by a rational isomorphism on the degree-one part of an abelian power

Let `B` lie over `S` and `C` over `T`, with `S → T` a map over the common
ground field. `powerMapOver` applies an actual abelian-scheme morphism
from `B` to the pullback of `C` on each factor and then projects to `C`.
`quasiIsogenyPullback` takes a rational isomorphism of these abelian
schemes over `S`, clears its denominator and takes the geometric étale
pullback along the resulting map of actual relative powers. It extends
the constant cohomology to the specified coefficient field and multiplies
by the inverse of the denominator to the power `m`.

On degree one in each factor, multiplication by an integer acts by that
integer on each factor's cohomology. The correction therefore has exponent
`m`, also when `m = 0`. The construction gives a linear map on the total
cohomology groups for a choice of denominator. The linear map is used on the
selected cohomology in the comparison with the actual coefficient system.

The geometric input is the rational isogeny equivalence in Harris–Taylor,
*The Geometry and Cohomology of Some Simple Shimura Varieties* (2001),
III.1, printed p. 91 (PDF p. 99). The rational scalar rule follows from the
relative first-cohomology description and the factorwise projector in
III.2, printed p. 98 (PDF p. 106). Literature ID
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
