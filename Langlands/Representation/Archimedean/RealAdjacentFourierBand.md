# The input band of an adjacent polynomial Fourier multiplier

In a pair of adjacent compact rotations, a polynomial of degree `d` in
one rotation generator contributes to mode `i` of the other rotation only
from input modes in `[i - d, i + d]`. The proofs use the same compact
rotation relations and polynomial model as `RealPolynomialFourierPropagation`.
The raising and lowering operators move a mode by one, so induction gives
the interval for a power of the adjacent generator. Summing the powers gives
the interval for a polynomial. The local coefficient result uses the exact
polynomial Fourier relation in a common finite degree. Applying it to every
compact rank-three coset gives the ambient result.

For the two outer rotations of `GL₄(ℝ)`, the proof retains the input
band at mode `i` on axis 0. It realizes this truncation and its polynomial
image by continuous right-compact-finite functions using
`RealSwapFLanding.exists_multiplier`. The one-axis result on their
differences shows that the mode-`i` coefficient of the axis-1 polynomial
image is unchanged by the truncation. For every axis-2 mode in the input
band at `j`, the axis-0 coefficients of the truncated function's axis-2
coefficient vanish. Inside the axis-0 band this follows from the assumed
rectangular vanishing and the disjoint coefficient law. Outside that band
it follows from the truncation multiplier. Finite Fourier uniqueness on
axis 0 therefore gives zero throughout the axis-2 input band. Apply the
one-axis result on axes 1 and 2 and commute the two outer coefficients to
obtain the double output coefficient in `RealAdjacentFourierBandStatement`.

This is a derived coefficient lemma used to compare the endpoint parities
of the linked two-block presentation.
