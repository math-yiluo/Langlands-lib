# The complex trace Fourier transform and Tate's integral identity

This internal module builds the target positive trace Fourier transform
on complex Schwartz space. It composes Mathlib's inverse Fourier transform
for the real inner product with `y ↦ conj (2 * y)` and multiplies by two.
The inner product of `x` with `conj (2 * y)` equals `2 * Re (x * y)`.
The resulting kernel is `exp (4πi Re (x * y))`, and the scalar converts
Lebesgue area to the target measure.

Multiplication by a nonzero complex number `a` has real determinant
`‖a‖²`, as given by the algebraic norm. The change of variables for this
map gives the zeta multiplier `direction(a)^(-m) * ‖a‖^(-2u)` for
precomposition of the test function by multiplication by `a`. Scaling
the Haar measure in the Fourier transform contributes the separate scalar
`c`.

On `0 < Re u < 1`, the proof of `tate_identity` expresses the product
of two zeta integrals with weights `(m, u)` and `(-m, 1 - u)` as one
iterated integral. Under `y = x * z`, the angular powers of `x` cancel,
and its radial exponent `-2` cancels the determinant `‖x‖²`. The slice
norms are integrable by the two convergence estimates. With a trace
Fourier transform in the second slot, a further application of Fubini
interchanges the two Schwartz functions, since `Re (w * (x * z))` is
symmetric in `w` and `x`. For this swap the norm-one character gives the
product of the Schwartz norms as a dominating function. This is the
complex version of the argument formalized in `RealTateIdentity.lean`.
