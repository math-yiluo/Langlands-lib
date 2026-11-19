# The diagonal character of the one-sided compact lift

`RealCompactParityLiftingStatement` starts with an actual compact-finite
standard-module vector `f` on `GL₄(ℝ)` and a vector with the middle
polynomial Fourier coefficients of `f`. Its primary axis is 0 or 2.
The input middle half-turn has sign `(-1)^H`. The polynomial image has
zero primary coefficients at indices `j ≥ N+H` with `N > 0`. The target
is an all-character module whose diagonal signs differ from the input
at just the two positions of the primary block.

The resulting vector in that module has zero middle coefficients for
`|j| ≥ H`. Its primary coefficients at `|j| ≥ N` equal those of `f`
with factor `1` at nonnegative indices and `-1` at negative indices.
The coefficient identities hold on the whole compact group.

The proof is derived from the ambient degree-layer lift and the block
Fourier reflection laws. The two input vectors have a common polynomial
degree bound on the compact group. The middle polynomial relation and
primary vanishing give the degree-layer hypothesis to
`RealAmbientAdjacentLifting`, yielding a kernel vector with the desired
positive high coefficients.

The roots of the middle differential tail polynomial are the integers
`2k−H+1` for `0 ≤ k < H`, by the falling factorial formula. The kernel
has coefficients only at these roots. Rotation by π in the middle
block therefore has eigenvalue `(-1)^(H−1)` on that kernel. The same
rotation reverses either adjacent outer rotation. The input eigenvalue
is opposite to the kernel eigenvalue, which gives the negative sign
on the negative high modes.

Each diagonal reflection preserves the polynomial kernel because it
either fixes or reverses the middle frequency. On high primary
coefficients of the kernel lift, its effect is the required target
sign. A reflection inside the primary block reverses the frequency,
and the high coefficient sign changes under that reversal. A
reflection outside the block leaves it fixed. Successive averages
with each reflection, weighted by its target sign, preserve the
kernel and the high coefficients. The reflections commute, so the
averages retain the sign equations already obtained.

The averaged compact polynomial is continuous and compact-finite.
Its sign equations give the full diagonal equivariance used by the
principal-series extension. The extension has the same compact
values, hence the same block Fourier coefficients, and lies in the
desired all-character standard module.
