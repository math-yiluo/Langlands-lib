# Evaluation of bounded Hilbert intertwiners

Let a group act unitarily on complex Hilbert spaces \(E\) and \(H\), and suppose
that \(E\) is topologically irreducible. Assume that the action on \(E\)
restricted along \(K \to G\) is continuous and admissible, and that it has a
nonzero \(K\)-finite vector. For any unit vector \(x_0 \in E\), evaluating a
bounded intertwiner \(T : E \to H\) at \(x_0\) is isometric for the operator
norm. `HilbertIntertwinerEvaluationStatement` gives a bounded linear left
inverse to this evaluation, defined on all of \(H\).

The proof places a nonzero \(K\)-finite vector in its finite-dimensional orbit
span. The restricted action there has continuous matrix entries because the
coordinate functionals on this span are continuous. Its inclusion in \(E\)
gives a nonzero element of a finite-dimensional space of \(K\)-intertwiners.
Postcomposition by a bounded operator commuting with \(G\) preserves that
space. An eigenvector of postcomposition takes some vector to a nonzero
eigenvector in \(E\). The eigenspace in \(E\) is closed and \(G\)-invariant, so
irreducibility makes the operator scalar.

For an intertwiner \(T\), unitarity makes its adjoint an intertwiner in the
reverse direction. Thus \(T^*T=c\,\mathrm{id}\). Evaluating its quadratic form
at \(x_0\) and using the operator norm identity for \(T^*T\) gives
\(\|T x_0\|=\|T\|\). The bounded intertwiner space is closed by the pointwise
intertwining equations, so its isometric evaluation has complete range.
Orthogonal projection onto that range followed by inverse evaluation gives
the stated bounded left inverse.

This internal result uses `GKModuleDensity.matrixRep` and its inclusion
identity. The eigenvector step uses the same finite-dimensional
postcomposition argument as `InfinitesimalCharacter.exists_eigenvector_of_commute`.
The application in the cuspidal multiplicity-one argument recovers an
operator family from the orbit of a single vector.
