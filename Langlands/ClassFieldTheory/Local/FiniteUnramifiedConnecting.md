# Connecting-map normalization of the finite unramified invariant

This module identifies the finite cyclic invariant with the computation
in Serre, *Local Fields*, Chapter XIII, §3, Proposition 6. It uses the
inverse of the connecting arrow from first cohomology with Q/Z coefficients
to second cohomology with integer coefficients, as specified by the official
correction to printed page 193.

Normalized valuation acts on the actual extension units equivariantly.
The norm is unchanged by each Galois automorphism, and its order is the
positive extension degree times the upper order. This gives equality of
orders in the upper field. The valuation of the image of a base unit is
its base order since the ramification factor is one.

For a positive carry class, write `z` for the order of its defining base
unit. Multiplying the standard residue representative of each cyclic
coordinate by `z` and dividing by the extension degree gives a rational
lift of a character into Q/Z. Its differential is `z` times the carry,
with the sign in the inhomogeneous cochain differential. This is the
cocycle induced by valuation. The connecting homomorphism therefore sends
the character to the valuation class, and applying the inverse and
evaluating at the chosen generator gives the finite invariant. All classes
have a carry representative, so the equality holds on the whole relative
cohomology group, including degree one.
