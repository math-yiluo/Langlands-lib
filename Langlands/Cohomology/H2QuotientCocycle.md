# Descent of an adapted two-cocycle

Author: Worker 138.

For any commutative ring, group G, normal subgroup S and representation A,
`descendRelativeCocycle A S c hc` constructs a two-cocycle on G/S with values in
Mathlib's actual quotient representation on the S-invariants of A. The input
`c` is an actual Mathlib two-cocycle, and `hc` says that c(s,g) and c(g,s) vanish
for all s in S and g in G. No cohomological vanishing assumption is used in this
construction.

The two-cocycle identity first shows that c(g,hs)=c(g,h), then that
c(gs,h)=c(g,h). Normality converts left multiplication by a subgroup element
to right multiplication, so the same identity shows that all values c(g,h)
are S-invariant. Two quotient lifts give the function on (G/S) × (G/S).
The cocycle identity for this function follows by choosing representatives
and applying the original identity; the action is exactly the quotient action
on invariant coefficients. `descendRelativeCocycle_apply` gives its value on
representatives, and `inflate_descendRelativeCocycle` proves that Mathlib's
actual inflation of the resulting cocycle equals c.

This is an internal construction for the explicit cocycle proof of generic
H2 inflation–restriction under H1 vanishing. The parent result is Serre,
*Local Fields* (1979), VII.6 Proposition 5, printed pages 117–118. Serre uses
dimension shifting there; the construction here is derived directly from the
inhomogeneous cocycle identity in Mathlib's `GroupCohomology.LowDegree`, not
claimed as a separately stated result in the source. All parameters live in
an arbitrary common universe, with no finiteness or trivial-action restriction.
