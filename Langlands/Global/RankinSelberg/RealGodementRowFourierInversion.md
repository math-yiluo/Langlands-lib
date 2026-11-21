# Opposite-parameter Fourier inversion for real rows

`RealGodement.realRowSchwartzFourier n a` constructs the positive real row
Fourier transform as a Schwartz test, including for a row with zero entries.
`realRowSchwartzFourier_apply` proves it evaluates to the existing
`ArchimedeanLocal.realFourierTransform a` with the actual product of the
self-dual scalar measure, not an independently chosen normalization.
`realRowSchwartzFourier_neg_comp` proves that the transform for `-a` undoes the
transform for `a`.

The proof first treats the scaled transform on a finite-dimensional real
Euclidean space. Its measure factor is `c = (sqrt |a|)^dim`, unchanged at
`-a`. In the outer Fourier integral substitute `u = a x`, obtaining one
inverse determinant Jacobian `|a|^(-dim)`. The two factors of `c` cancel
this Jacobian; the remaining integral is the ordinary Fourier transform of
the inverse Fourier transform on Schwartz space. Then transport through the
continuous linear row-coordinate equivalence. The product of the coordinate
self-dual measures pushes forward to the scaled Euclidean volume, and the
real inner product becomes the sum of coordinate products.

This is an internal normalization proof. It specializes the Library's
euclidean scaled transform and Mathlib's Schwartz inversion to the row
coordinate and measure of the real local integrals. The step is needed when
applying the opposite-sign column transform to Jacquet's dual test in
§8.3, (8.4). It asserts neither the dual recursion nor the local functional
equation.
