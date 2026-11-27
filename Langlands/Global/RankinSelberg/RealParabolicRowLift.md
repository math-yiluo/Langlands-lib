# The real parabolic Fourier moment on the leading block

For any Schwartz function of the last row of a real invertible matrix, a
Schwartz function on the upper off-diagonal rectangle realizes that row
function by the translated Jacquet Fourier moment. The kernel uses a
negative additive phase on the simple-root entry at the boundary between
the two blocks. Its absolute integral exists for every invertible first
block. Each column contributes one factor of the absolute determinant of
the first block to the change of variables.

On the Fourier side, extend the prescribed row function by multiplying it
by a Gaussian in the other columns, whose value at zero is one. Apply the
opposite-sign inverse transform to obtain the rectangle test. Left
multiplication by the inverse of the first block in the test transfers to
multiplication by the transpose of that block in the frequency. This
sends the boundary frequency to the last row of the first block in the
first column. The integrability proof uses the Schwartz pullback and the
unit modulus of the additive phase.

`rowFourierProfile` is the continuous linear map that takes the negative
rectangular Fourier transform and restricts it to first-column
frequencies. `parabolicMomentKernel_integral` gives the translated moment
formula for every Schwartz rectangle test. The extension by a Gaussian
and Fourier inversion prove surjectivity of the profile map.
`realParabolicCompactRowProfileDensity` follows from this surjectivity and
the density of compactly supported smooth functions in the Schwartz
topology of the rectangle.

This is the Fourier calculation in H. Jacquet, *Archimedean Rankin–Selberg
Integrals* (2009), Proposition 14.1, author-posted pp. 103–104, with the
boundary position given by the simple-root character in (2.2), p. 3.
It supplies the rectangle test for the split Jacquet integral.
The registered source is `jacquet-2009-archimedean-rankin-selberg`, SHA-256
`7a11766eadf25fb7452ce7faa193469791796f572fc654c8fe90a8608bb46afe`.
