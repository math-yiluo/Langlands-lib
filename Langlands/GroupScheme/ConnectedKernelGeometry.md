# Geometric connectedness from the actual kernel

The theorem `connectedKernelHomGeometry` proves the published proposition
`ConnectedKernelHomGeometryStatement` at every universe `u`, over an arbitrary
scheme base. A group-scheme homomorphism that is surjective on scheme points
and whose actual kernel is geometrically connected is geometrically connected.
No flatness, finiteness, smoothness, or commutativity assumption enters this theorem.

The implemented proof uses the published kernel-pair square
`KernelPair.isPullback_scheme q`. Its first projection is the base change of the
kernel's structure morphism, hence is geometrically connected. The published
`AlgebraicGeometry.GeometricallyConnected.descendsAlong_surjective` descends this
property along the surjective homomorphism. The exact proposition proof introduces
its hypotheses and calls this lemma.

The subgroup-preimage corollaries use the actual pullback from
`Reductive.UnipotentRadicalQuotientReduction`. Geometric connectedness of its
projection follows by base change. If the original homomorphism is smooth, so
is this projection; its underlying map is therefore open. Mathlib's
`GeometricallyConnected.connectedSpace` then makes the inverse image of a
connected subgroup connected. A final corollary replaces the original
homomorphism's geometric-connectedness hypothesis by a geometrically connected
kernel and scheme-point surjectivity.

This is internal derived content, using only the imported published actual group,
kernel, pullback, geometric connectedness and smoothness APIs. The statements
concern all field-valued geometric fibers and scheme surjectivity. They do not
assert surjectivity on every test's group of points. The parent quotient
construction, affineness, and unipotent extension arguments remain separate.
