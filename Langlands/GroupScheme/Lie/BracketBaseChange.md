# Lie brackets under field extension of the base scheme

For an affine, locally finite-type group scheme \(G\) over a field \(k\) and a
field extension \(K/k\), `Lie.kernelBaseChangeLieEquiv` compares the Lie algebra
of the pullback \(G_K\) over \(K\) with the actual tangent kernel of \(G\) on
\(K\)-dual numbers. The underlying linear equivalence is
`Lie.kernelBaseChangeLinearEquiv`, induced by the pullback equivalence on
points.

The proof uses `Lie.finiteCoordinates` for \(G\) and their pullback for
\(G_K\). Evaluation in the pulled-back coordinates agrees with evaluation in
the original coordinates after applying the kernel comparison. The adjoint
tangent matrices agree by `Lie.adjointRepresentation_baseChange_tangentMatrix`.
On each side, multiplying this matrix by the coordinates of a second tangent
point gives the coordinates of their Lie bracket by
`Lie.adjointKernelDifferential_mulVec`. Injectivity of the coordinate
equivalence then gives bracket compatibility.
