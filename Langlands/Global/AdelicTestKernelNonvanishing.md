# Compact smooth adelic kernels detect a nonzero value

`Langlands.Global.AdelicGroupPoints.adelicTestKernelNonvanishing` proves
`AdelicTestKernelNonvanishingStatement`. If a continuous complex-valued
function on the adelic points of a smooth affine group over a number field
is nonzero at the identity, its right convolution with some compact smooth
adelic test kernel is nonzero there.

The auxiliary `exists_nonnegativeTestKernel` constructs a real nonnegative
kernel, positive at the identity, with support in any identity neighborhood.
The adelic product decomposition gives a product neighborhood. The infinite
factor uses a smooth bump function and the finite factor uses the indicator
of a compact open subgroup. The latter supplies both finite translation
invariances. Given an input function, the proof takes a neighborhood where
its product with the conjugate of its value at the identity has positive
real part. The convolution integral multiplied by that conjugate then has
strictly positive real part.

This gives the local test-kernel step in the compact-convolution argument
of Mœglin–Waldspurger, *Spectral Decomposition and Eisenstein Series*
(1995), I.3.4, p. 46.
