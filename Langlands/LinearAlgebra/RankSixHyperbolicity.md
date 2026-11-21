# Hyperbolicity from an isotropic plane in dimension six

Worker 863, Task 7498.

`RankSixHyperbolicityStatement` assumes a nondegenerate symmetric form of
dimension six over a field where two is invertible. It assumes two independent
orthogonal isotropic vectors and a basis in which the Gram determinant is the
negative of a square. The associated quadratic form is isometric to the
orthogonal sum of three standard hyperbolic planes.

Split off the first isotropic vector with a normalized partner. The second
isotropic vector projects to a nonzero isotropic vector in the orthogonal
complement because it is orthogonal to, and independent of, the first vector.
Split off a second hyperbolic plane using that projection. The remaining form
has dimension two. The two hyperbolic factors cancel in the determinant, and
a change of Gram basis multiplies the determinant by a square. In an orthogonal
basis the remaining form therefore has diagonal values `a,b` with `ab = -s²`.
Since `a ≠ 0`, the vector with coordinates `s/a,1` is isotropic. The third
hyperbolic split has zero-dimensional complement, giving the asserted isometry.

This is the maximal Witt index step in Springer, appendix to M. Kneser,
*Lectures on Galois Cohomology of Classical Groups* (1969), Theorem 5.3.3(i),
printed p. 109 (PDF p. 115).
