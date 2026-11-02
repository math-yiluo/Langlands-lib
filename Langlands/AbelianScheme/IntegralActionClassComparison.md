# Integral criterion for rational action class equality

This internal comparison works on the same actual abelian schemes `B` and
`C` over an arbitrary base scheme. It uses the existing rational algebra
action category and its existing quotient by actual equivariant rational
isomorphisms.

`IntegralActionInverseData a a'` consists of actual integral maps between
`B` and `C` in both directions, a common nonzero integer, and exact
equations saying that both composites are that multiple of the respective
identity and both maps intertwine every element of the integral ring.
It contains no input rational isomorphism.

`IntegralActionInverseData.baseChange` transports supplied data along any
actual scheme morphism. Applying the additive abelian-scheme pullback
functor preserves the nonzero integer and all four kinds of equations.
The three projection lemmas identify the unchanged integer and the
actual pulled-back maps.

Let `O` be a full integer lattice subalgebra of a rational algebra `A`,
with integer basis `b`. The two integral actions extend to rational
`A`-actions by the existing `integralActionRationalExtension`.
`integralActionInverseDataIso` produces an isomorphism of those rational
actions from exact integral inverse-multiple data. The underlying rational
forward map is the rationalization of its actual integral forward map;
its inverse is the rationalized integral reverse map divided by the
common nonzero integer. The existing extension theorem promotes exact
integral equivariance to equivariance for every element of `A`.

If the basis is finite, `integralAction_classOf_eq_iff` proves that equality
of the two classes in the existing rational-action quotient is equivalent
to nonemptiness of `IntegralActionInverseData a a'`. From class equality,
the quotient's existing criterion supplies an actual rational equivariant
isomorphism. `integralActionRationalIsoData` gives exactly equivariant
integral representatives; retain their maps and the nonzero product of
their denominators. Conversely, `integralActionInverseDataIso` gives
the required rational equivariant isomorphism.

The result preserves the actual representatives and uses no Hom
torsionfreeness assumption. It does not assert that arbitrary rational
actions have integral models, that the integral forward map is an
isomorphism, or that it is a geometric isogeny. Polarization, adelic
level and moduli representability comparisons remain separate obligations.
