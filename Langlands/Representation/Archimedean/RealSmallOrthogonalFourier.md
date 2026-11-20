# Sign and low-mode averages as weighted orthogonal Haar integrals

`determinantWeight ε` is continuous and takes the values `1` and `ε` on the
orthogonal components of determinant `1` and `-1`. In dimension one the Haar
probability formula identifies integration with this weight with the signed
average of the two point values.

For a two-dimensional induced block of weight magnitude `m`, the sign at the
first coordinate is `ε = (-1)^(m+1)` and the second sign is one. The phase read
from the second row of a matrix `k` is `k₁₁ + i k₁₀`, with indices starting at zero.
It is nonzero by the row orthogonality equation. At a rotation by `θ` and at its
left translate by the first-coordinate reflection it is `exp(iθ)`. The continuous
`pairDensity m` multiplies the determinant weight by the sum of the negative
Fourier powers of that phase over the parity window `window m`.

The product of the two coordinate reflections is the rotation by π. In the
four-sign average, two terms are thus shifts by π of the rotation or reflected
rotation integrands. The existing coefficient translation formula gives a factor
`(-1)^j` for each such shift of the `j`-th coefficient. Using `ε² = 1`, the
coefficient is zero outside the parity `j + m + 1` even. At that parity it is
half the sum of the rotation coefficient and `ε` times the reflected rotation
coefficient. After normalization by `2π`, the Haar probability formula on `O(2)`
identifies this with the integral of the corresponding phase power and determinant
weight against the test. The finite sum over `|j| < m` gives `integral_pairDensity`.

Negating the indices permutes `window m`. Hence the weights at rotations by `θ`
and `-θ` are both the same sum of `expMode j θ` over the window. Conjugation of
the inverse rotation by an orthogonal frame gives one of these two orientations,
so it has the same weight. This internal calculation supplies the one- and
two-dimensional weights for the continuous compact projection expansion in the
Cartan trace argument.
