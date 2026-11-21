# Weak approximation for rational invertible matrices

`RationalGLWeakApproximationStatement` gives density of
\(\mathrm{GL}_n(K)\), for a number field \(K\), in the product of the
actual \(\mathrm{GL}_n(K_v)\) at any finite set of finite places.
The map is entrywise scalar extension, and the target uses the
product of the matrix-unit topologies.

The proof first lifts a dense scalar diagonal into a finite family
of \(T_1\) topological fields to the matrix diagonal. It applies the
scalar density at each matrix entry and rearranges the finite
products. Each map from invertible matrices to matrices is an open
embedding, so a neighborhood of local invertible matrices has open
image near its tuple of underlying matrices. A rational matrix
approximating that tuple has nonzero determinant because its image
at one of the specified places has nonzero determinant. For an
empty set of places the identity matrix gives the approximation.
The number-field scalar diagonal comes from the published weak
approximation theorem for the actual completions, followed by
projection onto the chosen finite factors.

This internal result supplies the rational approximation used in
the elliptic comparison of Arthur–Clozel 1989, Chapter 1, p. 46, and
Henniart–Lemaire 2011, I.6.8.
