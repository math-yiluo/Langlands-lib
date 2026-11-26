# Uniform convolution equations from finite-dimensional coordinates

`Langlands.Global.AdelicGroupPoints.HasConvolutionEquationAt K f s₀` is
the existence of one uniform convolution equation for a family \(f_s\) of
complex functions on the actual adelic group. The fixed kernels are smooth,
compactly supported and bi-finite under the indicated archimedean subgroup.
The coefficients are entire, the right-hand coefficient is nonzero at \(s_0\),
and the equation holds pointwise for every \(s\).

`hasConvolutionEquationAt_of_finiteModel` applies to continuous functions
\(f_s\). It assumes that convolution by a fixed bi-finite test kernel \(h\)
preserves a subspace \(W_s\) containing \(f_s\). Injective linear coordinates
on \(W_s\) intertwine this restricted action with a square matrix \(B(s)\).
The matrix has entire entries and is invertible at \(s_0\). The coordinates
may take values in a larger space than their image.

The proof forms the characteristic polynomial of the matrix over the
subring of entire functions. Specialization commutes with the polynomial and
its coefficients. Cayley–Hamilton annihilates the convolution operator on
\(W_s\) by injectivity. The positive powers act by the kernels from
`positiveConvolutionPower`, and the proof moves the constant term to the
right as a scalar multiple of \(f_s\). Its value at \(s_0\) is nonzero by the
determinant identity. The proof never divides by that scalar.

The finite-dimensional step comes from Mœglin–Waldspurger, *Spectral
Decomposition and Eisenstein Series*, I.4.5, printed pp. 60–62, especially
the characteristic polynomial and identity (7). The chapter file is
`05.4_pp_49_77_Upper_bounds_as_functions_of_the_constant_term.pdf`
in `moeglin-waldspurger-1995-spectral-decomposition` (collection fingerprint
`1ba99fb90916a687503e88c7191dad43b9c4865b68e6b4221a4f2126f2d2f141`,
chapter SHA-256 `a72fe12ffc7707cc35e91375a8fc9dc62c35570afbbb061c0e7ff6db99a90d3d`).
The entire-coefficient equation is the form used by Bernstein–Lapid,
*On the meromorphic continuation of Eisenstein series*, §8.3, Lemma 8.3,
journal p. 223 (`bernstein-lapid-2024-meromorphic-continuation-eisenstein-published`,
SHA-256 `6acbe78adf3a7ddff4be0caa92b169f0e609d1245f674a71fbc6989d6aef9268`).
This formulation takes the coordinate space, its action and the nonzero
determinant at \(s_0\) as premises.
