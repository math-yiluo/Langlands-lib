# Decomposition of smooth complex kernels into real matrix tests

Every smooth compactly supported complex function on the real general
linear group is the sum of a real matrix test and \(i\) times another
real matrix test, evaluated on the underlying real matrices.

The extension by zero is smooth on the open invertible matrices. Its
support is contained in the image of the original compact support
under the inclusion of the units. That image is compact and contained
in the open units, so the extension vanishes on a neighborhood of
each singular matrix. The extension is therefore a complex-valued
smooth test on the open set. Taking real and imaginary parts gives
the two real tests.

This internal construction uses the existing smooth restriction
theorem for the units chart and Mathlib's test function space.
