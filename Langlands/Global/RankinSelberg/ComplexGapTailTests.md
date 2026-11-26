# Prescribed tests for the retained tail

`ComplexGapTailTestsStatement t q` prescribes a standard polynomial Gaussian on the leading rectangle and a polynomial Gaussian on each observed tail column. At unit trace scale, `complexGapTailTests` realizes them by a split test that is a standard matrix polynomial Gaussian on the full rectangle.

The last input column supplies the first observation without a transform. For the other columns the proof applies inverse trace Fourier transformation with the opposite scale and reverses their order to match the tail factor. Fourier transformation at unit scale preserves the standard polynomial Gaussian space. A product of the resulting column polynomials and the leading polynomial, with column indices placed in the full rectangle, gives the required matrix test.

For the integrability argument, `exists_halfTailTest` realizes the Gaussian with half the standard exponent using the same Fourier inversion and arbitrary Schwartz columns. `retainedHaar_isOpenPosMeasure` proves positivity on nonempty open sets from the positive chart densities and the open-set positivity of each Haar factor.
