# Locally unipotent automorphisms fix idempotents in characteristic zero

This is an internal derived helper for the characteristic-zero unipotent
connectedness argument. Its topology and ring results are consequences of
Mathlib's finite irreducible-component theorem for Noetherian spaces and its
equivalence between idempotents of a commutative ring and clopen subsets of its
prime spectrum.

A clopen subset is a union of irreducible components: each irreducible component
is preconnected and hence lies entirely inside or outside the clopen subset.
It follows that clopen subsets inject into subsets of the finite set of
irreducible components. Thus there are finitely many clopen subsets, and a
commutative Noetherian ring has finitely many idempotents.

For a characteristic-zero algebra with finitely many idempotents, an algebra
endomorphism with an algebra endomorphism as right inverse acts surjectively on
the finite type of idempotents. That action is bijective, so each idempotent is
periodic. If the linear endomorphism is locally unipotent, the periodic-vector
lemma in `CharZeroPeriodic` shows that it fixes the idempotent. The lemma assumes
local nilpotence of the difference from the identity on every algebra element;
it does not assume a uniform exponent or finite-dimensionality of the algebra.
