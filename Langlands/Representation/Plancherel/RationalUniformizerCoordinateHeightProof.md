# Proof of uniformizer coordinate height

`Langlands.Plancherel.rationalUniformizerCoordinateHeight` proves the exact
`RationalUniformizerCoordinateHeightStatement` at independent field and
coordinate universes.

First, `rationalCharacter_rationalMatrixNorm_bound` represents a character as
the regular function obtained by evaluating it at the identity morphism of its
source scheme. Naturality of character evaluation identifies its pullback at
an actual rational point with the character value. The regular-function power
bound from `RationalMatrixNormComparison` gives a uniform polynomial estimate.
That imported development is by Worker 1633; it is used without duplicating its
proof here.

For the uniformizer chart, restrict the closed matrix embedding along the
supplied closed inclusion of the commutative group scheme. Apply the character
bound to `-α`. The intrinsic uniformizer evaluation formula identifies its
normalized magnitude with `q^⟨α,sum_j m_j x_j⟩`. Linearity of the integral pairing
and positivity of each generator pairing show that this exponent is at least
`sum_j m_j`. Since `q > 1`, comparison of integer powers gives the conclusion.
Restriction of rational matrices identifies the resulting norm with the
specified ambient norm. The empty coordinate family is handled by the same
finite sums and the identity point; no nonempty-coordinate assumption is used.

This is an internal proof of the supplied-chart estimate. It neither chooses
the chart generators nor establishes a global Cartan cover or coefficient
bound.
