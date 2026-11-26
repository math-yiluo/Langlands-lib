# Invertibility on a finite-dimensional convolution space

`Langlands.Global.AdelicGroupPoints.ConvolutionApproximates kernels S`
says that the smooth test kernels with the indicated property approximate
every finite family in the continuous function subspace \(S\), uniformly
on each compact set.

`exists_injective_rightConvolution_of_approximation` assumes that \(S\) is
finite-dimensional and that the indicated test kernels preserve it.
A finite list of point evaluations gives coordinates on \(S\).
Approximation of the coordinate basis at those points puts the matrix
of a suitable convolution operator in a neighborhood of the identity
where the determinant is nonzero. The restriction is therefore
injective, including the case of a zero-dimensional \(S\).

`IsIwasawaCompact.hasConvolutionEquationAt_of_averaged_stability` applies
this criterion to the Iwasawa twists of a fixed space. It assumes two
continuous \(K_\infty\)-weights, each with finite left translate span,
that reproduce the base fibre under direct and inverse translation
respectively. It also assumes that every kernel averaged on both sides
with these weights preserves the space after transporting convolution
back through any of the twists. The approximation theorem supplies an
averaged kernel injective on the base fibre. Compact averaging gives
bi-finiteness and the finite-dimensional characteristic-polynomial
argument gives the entire-coefficient equation. The invariant
finite-dimensional space is a premise of this implication.

This implements the determinant step of Mœglin–Waldspurger, *Spectral
Decomposition and Eisenstein Series*, I.4.5, printed pp. 60–62, in
particular the passage from approximation at fixed evaluations to the
characteristic polynomial
(`moeglin-waldspurger-1995-spectral-decomposition`, collection fingerprint
`1ba99fb90916a687503e88c7191dad43b9c4865b68e6b4221a4f2126f2d2f141`,
chapter `05.4_pp_49_77_Upper_bounds_as_functions_of_the_constant_term.pdf`,
SHA-256 `a72fe12ffc7707cc35e91375a8fc9dc62c35570afbbb061c0e7ff6db99a90d3d`).
