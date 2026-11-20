# Entire normalized product Tate reflection

`ComplexTateProductEntireReflectionStatement` extends the positive trace Fourier identity for the normalized product Tate integral to all complex exponents. It applies to any entire normalization in the sense of `IsEntireNormalization`, including the one constructed by `complexTateProductEntireFamily`.

For a given exponent vector, the proof chooses a complex affine line with real slopes that places every real part at one half at parameter one. A neighborhood of that point lies in the common strip, so the two entire restrictions agree there by the full product Tate identity. The one-variable identity theorem gives their equality at parameter zero, the original vector of exponents.

This derives the diagonal continuation step for Jacquet, *Archimedean Rankin–Selberg Integrals* (2009), §4.7, equation (4.3), from the scalar Tate continuation and the common-strip product identity.
