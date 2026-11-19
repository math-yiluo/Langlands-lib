# Angular Gaussians for the complex Tate zeta integral

This internal proof module supplies the Gaussian formulas in
`ComplexArchimedeanTateStatement`. The Gaussian of weight `m` is the adapted
Gaussian of `Langlands.Global.Hecke.ArchGaussian` at scale one, divided by
`π`. The comparison splits the integer weight into nonnegative and negative
cases.

For the Schwartz witness, the real quadratic exponent has temperate
growth on the complex plane. The bound for the derivatives of a
composition applies to the real exponential, whose derivatives are all
the exponential. Each resulting derivative bound is the radial Gaussian
times a power of `1 + ‖z‖` with an order-dependent constant. The Library
Gaussian decay estimate absorbs that power and the additional power of
`‖z‖` in the Schwartz seminorm. The proof then includes the real-valued
radial Gaussian into `ℂ` and multiplies it by the angular monomial, which
has temperate growth because the identity and conjugation are real linear.

The Fourier calculation writes the positive trace kernel as
`Real.fourierChar` at `2 * (z * y).re` and applies the Library Fourier
integral. The factor two from the target measure cancels the factor one
half in that integral. The resulting Gaussian has weight `-m` and
coefficient `I ^ m.natAbs`. For the zeta integral, the origin has measure
zero and the angular character agrees away from it with `complexCharFun`
at spectral parameter zero. The Library Gamma integral contributes
`π / 2`, which cancels the two from the measure and the inverse `π` in the
Gaussian.

The formulas specialize the complex Gaussian computations in Tate's
thesis, §2.5, printed pp. 316–319, registered as `tate-1967-thesis`. The
target normalization and the source's Fourier sign are recorded in
`Statement.md`.
