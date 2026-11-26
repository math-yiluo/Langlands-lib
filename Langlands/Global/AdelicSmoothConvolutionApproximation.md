# Approximation by smooth adelic convolution kernels

On the actual adelic point group of a smooth affine group over a number
field, `exists_normalizedAdelicTestFunction` constructs a nonnegative test
kernel of Haar integral one supported in any identity neighborhood.
`AdelicConvolutionApproximationStatement` uses these kernels to approximate a
finite family of continuous functions uniformly on a specified compact set
by right convolution.

The archimedean factor is a smooth bump at the identity. The finite factor
is the indicator of a compact open subgroup contained in the chosen
finite-adelic neighborhood. Their product has compact support and is
positive at the adelic identity. Its Haar integral is therefore positive
and finite, so division by the integral normalizes the kernel. For
approximation, joint continuity and compactness give a single identity
neighborhood in which the right translates of every input differ from that
input by at most the specified tolerance at every point of the compact
set. Integrating this bound against the normalized nonnegative kernel
gives the estimate.

This is the smooth approximate identity used before imposing compact
finiteness in Mœglin–Waldspurger, *Spectral Decomposition and Eisenstein
Series*, I.4.5, printed p. 61
(`moeglin-waldspurger-1995-spectral-decomposition`, collection fingerprint
`1ba99fb90916a687503e88c7191dad43b9c4865b68e6b4221a4f2126f2d2f141`,
chapter `05.4_pp_49_77_Upper_bounds_as_functions_of_the_constant_term.pdf`,
SHA-256 `a72fe12ffc7707cc35e91375a8fc9dc62c35570afbbb061c0e7ff6db99a90d3d`).
