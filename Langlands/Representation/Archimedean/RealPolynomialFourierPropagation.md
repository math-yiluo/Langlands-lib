# Polynomial Fourier multipliers and adjacent mode bounds on O(3)

This internal bridge concerns continuous right compact-finite functions
`f,g` on `GL₃(ℝ)`. Suppose their Fourier coefficients along one adjacent
rotation differ by multiplication by a polynomial `Q(j)`. If the coefficients
of `f` along the other rotation vanish for `|j|>=n`, those of `g` vanish for
`|j|>=n+Q.natDegree`.

Restrict both functions to `O(3)` and place them in a common finite space of
polynomial functions of bounded degree. The published mode projections and
compact generators act on that space. Polynomial evaluation at `-i` times
the first generator multiplies its `j`-mode by `Q(j)`. The Fourier hypothesis
and completeness of the finite mode decomposition identify the restriction
of `g` with this polynomial applied to the restriction of `f`.
The proved algebraic finite-propagation bound then controls the other
generator's modes, and the normalized projection formula recovers the
claimed Fourier coefficient vanishing.

`RealPolynomialFourierPropagationStatement` is this universally quantified
polynomial multiplier assertion, proved by `realPolynomialFourierPropagation`.
The helper `tail_propagation` applies it to an actual rank-three Frobenius map
whose tail has positive cutoff `ell`, reduced resonant parity, and symmetry
sign `(-1)^ell`. On the source parity class, the scalar tail-polynomial
identity supplies the required coefficient relation. Off that class the
source coefficients vanish. Thus a low bound `n` for the other rotation
becomes a low bound `n+ell` for the actual output.

This module does not transport the result to arbitrary ambient rank.
No linked filtration or kernel-image containment is asserted.
