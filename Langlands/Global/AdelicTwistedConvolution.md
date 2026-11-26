# Entire dependence of convolution on the Iwasawa parameter

For continuous \(\phi\) on the actual adelic group, define \(T_\lambda\phi\)
by multiplication with the Iwasawa height power. The equivalence
`IsIwasawaCompact.continuousParameterTwist` has inverse division by that
power. The endomorphism `IsIwasawaCompact.twistedConvolutionEnd` is
\(T_\lambda^{-1}\delta(h)T_\lambda\) for a fixed smooth compact test kernel.

`IsIwasawaCompact.differentiable_rightConvolution_parameterTwist` proves that
\(s\mapsto \delta(h)T_{e(s)}\phi(x)\) is entire for each point \(x\) and complex
linear parameter map \(e\). The proof restricts Haar measure to the compact
support of \(h\). On each compact set of parameters, joint continuity bounds
the integrand on the product with that support. Every integrand is entire
in \(s\), since the height power at a point is the exponential of a complex
linear form. The bounded parametric integral theorem gives complex
differentiability. The same argument gives entire point evaluations of the
transported operator by division by the nonvanishing height power.

If one finite-dimensional subspace contains \(\phi\) and is preserved by the
transported operators at every parameter, a fixed collection of point
evaluations gives coordinates on it. Thus its convolution matrix has entire
entries. Injectivity at \(s_0\) gives a nonzero determinant there, and the
finite-dimensional convolution theorem yields the equation on \(T_{e(s)}\phi\)
for every \(s\).

This implements the point-evaluation step in the characteristic-polynomial
argument of Mœglin–Waldspurger, *Spectral Decomposition and Eisenstein Series*,
I.4.5, printed pp. 60–62
(`moeglin-waldspurger-1995-spectral-decomposition`, collection fingerprint
`1ba99fb90916a687503e88c7191dad43b9c4865b68e6b4221a4f2126f2d2f141`,
chapter `05.4_pp_49_77_Upper_bounds_as_functions_of_the_constant_term.pdf`,
SHA-256 `a72fe12ffc7707cc35e91375a8fc9dc62c35570afbbb061c0e7ff6db99a90d3d`).
