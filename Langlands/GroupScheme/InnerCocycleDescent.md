# Effective inner descent of a natural cocycle

Let `G` be a group scheme over `B`, let `p` be the structure morphism of a
cover `U`, and let `ξ` be a natural cocycle of `G` on `U`. The double-overlap
isomorphism `innerOverlap ξ` identifies the pullbacks of `G_U` by conjugation
with the inverse of the cocycle value at the two projections to `U`.
`innerDatum ξ` packages this isomorphism and its Čech cocycle law as an actual
`Descent.Datum` on `G_U`.

The overlap is built from the comparison isomorphisms for iterated base
change and the group automorphism given by conjugation over the double
overlap. A point of an iterated pullback is determined by its original
group point and base coordinate. The proof uses this description to evaluate
the pulled overlap on the triple pullback. The two successive conjugations
compose to the conjugation for the outer pair by the cocycle law of `ξ`.

If `B`, `U` and the underlying scheme of `G_U` are affine, and `p` is flat
and surjective, `innerTwist ξ` applies effective affine descent to the datum.
The pullback isomorphism `innerTwistIso` supplies the local charts of
`Cocycle.InnerTwist ξ`. Evaluating the solution's compatibility equation on
any two cover points gives the required conjugation transition on that test.

This internal construction uses the Library's actual group-scheme pullbacks
and effective affine descent. It supplies the inner forms used to compare
pairs of cocycles in the simply connected and adjoint Hasse problems.
