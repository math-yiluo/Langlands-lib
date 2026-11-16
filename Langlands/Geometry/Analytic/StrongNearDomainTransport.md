# Berkovich test relations and actual domain inclusions

This internal prerequisite works over a complete ultrametric normed field.
For an actual analytic domain `D` of a saturated presentation `B`, a test
triple of `B.domain D` retains an ambient chart, its original function and
its positive bound. `TestTriple.ambient` records that triple on `B`.
Its locus lies in `D`, and the domain locus is its inverse image under the
literal subspace inclusion.

For two full strong maps from any saturated source into `B.domain D`,
`strongNear_comp_domainInclusion_iff` identifies their Berkovich strong
test relation with the ambient relation after the canonical analytic
inclusion. Admissible test pieces are the same. Their inverse images and
covering conditions agree. The existing complete bounded-pullback formula
for domain inclusions identifies the two differences of pulled-back
functions, so their pointwise bounds also agree.

The derivation uses the existing actual domain atlas and strong-map
composition APIs. It does not infer analytic maps or equality of their
bounded pullbacks from their underlying point maps.

The source can also be restricted to an analytic domain containing the
whole inverse image of the test locus. Every original test piece lies in
that domain and therefore remains a chart of its actual domain atlas.
The complete pullback formula for precomposition with the inclusion keeps
the same pointwise bound.

Finally, precomposition with any downward-closed locally refining source
subatlas preserves `StrongNear`. Local refinement replaces an original
covering test piece by a selected chart containing the point and lying
inside that piece. The two map images still lie in the test locus, and
the bound on each selected chart is the corresponding original bound.
No hypothesis requires that the old covering charts be retained whole.
