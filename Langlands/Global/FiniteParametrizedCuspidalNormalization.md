# Normalization of finite cuspidal block coefficients

The positive Levi modulus is the pairwise product of idelic determinant
norms with exponents given by the block sizes. Form the same character on
a tuple of determinant idele classes and take the inverse of its positive
half. Its coordinate restrictions are Hecke characters. Multiplying the
coordinate values recovers the inverse half because the tuple is the
product of its one-coordinate insertions. Evaluating the tuple on the
actual adelic Levi determinant classes gives the inverse half-modulus
of that Levi. This identity also holds after inserting finite parabolic
points into the full adelic parabolic.

Twist each actual cuspidal realization by its corresponding determinant
Hecke character. The tensor of the resulting finite-action comparison
maps transforms by the product of these characters. In normalized
finite parabolic covariance that product cancels the positive half.
`normalizedCuspidalCoefficientEquiv` is the resulting equivariant
linear equivalence from unnormalized coefficients to the normalized
coefficients of the actual twisted cuspidal blocks.

This implements the inducing twist in Langlands, *On the notion of an
automorphic representation*, Corvallis Part I (1979), proof of
Proposition 2, printed p. 205 (PDF p. 200), source
`langlands-1979-notion-automorphic-representation`. The positivity and the
inverse in this comparison are fixed by the Library's normalized induction
covariance equation.
