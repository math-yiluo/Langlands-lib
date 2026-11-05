# Adapters for the triangular-kernel construction

This internal helper module connects the published concrete block group schemes
to the hypotheses used in constructing a solvable group's unipotent part.

The imported `TriangularLayer.triangularWeights_injective` proves that the weights `i ↦ -i` on `Fin N`
are distinct by cancelling negation and the integer coercion, then using
extensionality of `Fin N`.

`isSplitTorus_triangularLevi` applies the existing
`GeneralLinear.diagonalTorusIso` with these distinct weights. Its inverse
exhibits the block Levi as the split torus indexed by `ULift (Fin N)`.
The universe lift keeps the index in the base scheme's universe.

For arbitrary finite matrix indices and arbitrary integer weights,
`GeneralLinear.isAffineHom_blockUnipotentScheme` and
`GeneralLinear.locallyOfFiniteType_blockUnipotentScheme` use the existing closed
inclusion of the block unipotent group into the general linear group. Closed
immersions are affine and locally of finite type. The general linear group is
affine by its existing construction and smooth by
`GeneralLinear.smoothStatement`, hence locally of finite type. Composition and
the triangle equation for a morphism over the base give the two claims.

These are derived interface lemmas, not additional source assertions.
Their inputs are the existing Library constructions and proofs, and their role
is to supply the hypotheses of closed-subgroup unipotence and split-torus
triviality in the final kernel construction. The existence theorem is assembled
in `Langlands.GroupScheme.Absolute.SolvableUnipotentPart`.
