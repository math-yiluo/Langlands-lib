# Inversion for the scalar complex trace Fourier integral

`complexScalarFourier` uses the positive pairing
`(y,z) ↦ exp(2πi Tr_ℂ/ℝ(a y z))` and the Library's self-dual measure
`2‖a‖` times area. `complexScalarFourierSchwartz` realizes it pointwise on
Schwartz functions.

The proof writes the trace pairing as the real inner product of `y` with
`conj(2 a z)`. This turns the positive transform into the usual inverse
Fourier transform followed by that linear equivalence and multiplication by
`2‖a‖`. For inversion, the change of variables `z ↦ conj(2 a z)` scales area
by `(2‖a‖)^(-2)` in the pushed-forward measure. The two self-dual measure
factors cancel this Jacobian. The remaining integral is Mathlib's Fourier
inversion formula.

This is the scalar Fourier normalization needed for the triangular matrix
marginals. In particular the integral of the positive transform is the value
of the original Schwartz function at zero.

Negating the character parameter negates the argument of the trace character
and preserves the self-dual measure. These comparisons also identify the
negative rectangular Fourier transform.
