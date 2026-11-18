# Difference of cocycles in an inner form

Let `ξ` be a natural cocycle of a group scheme `G` on a cover `U`.
`Cocycle.InnerTwist ξ` supplies a group scheme `H` on the original base
and local group isomorphisms from its points to those of `G`. The charts
are natural in the test scheme. The change of chart from a cover point
`a` to a cover point `b` acts by conjugation with `ξ(a,b)⁻¹`.

For another cocycle `ζ`, `InnerTwist.difference` is a cocycle of `H` on
`U`. In the chart at `a` its value on `(a,b)` is `ζ(a,b) ξ(a,b)⁻¹`.
For the cocycle law, one transports the value at `(b,c)` to the chart at
`a` by conjugation with `ξ(a,b)` and then uses the original two cocycle laws.

`cohomologous_iff_difference_isTrivial` identifies pairwise cohomology
of `ξ` and `ζ` with triviality of the difference. A twist cochain `f`
corresponds to the coboundary cochain whose chart over `U` is `f⁻¹`.
Naturality gives its chart at each cover point, and the transition
identity gives its chart at the other point in the pair. Inverting
this correspondence recovers `f` from a trivialization of the difference.

The supplied charts and the difference commute with base change and
restriction to any compatible cover. The comparison uses the canonical
multiplicative bijections of points from the pullback adjunction. In
particular, cohomology after base change makes the difference trivial
on that pullback cover.

This internal interface isolates the cocycle calculation used in the
number-field Hasse problem. Constructing an inner form and chart by
effective descent is a separate step.
