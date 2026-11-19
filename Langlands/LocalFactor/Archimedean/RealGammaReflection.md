# Real Gamma ratios in principal-series positions

The formulas compare inverse normalized Gamma ratios for real characters and
real induced blocks under the positive-character convention. The arguments
already include the character exponent or the sum of exponents in a tensor
product. The identity holds at points where the displayed auxiliary complex
Gamma denominators are nonzero.

The comparison supplies the Gamma part of Jacquet's Appendix Lemmas 16.1 and
16.3 for the parities of the Library's position characters. The proof starts
from Mathlib's duplication and reflection formulas for the Deligne Gamma
functions. It writes a character ratio as a parity-dependent cosine or
`-i` times sine divided by the reciprocal complex Gamma function. Adding an
integer to the argument toggles the parity according to the integer and
multiplies the trigonometric numerator by a power of `-i`. This proves the two-
and four-character identities with the matching induced block weights.

The Lean proofs establish the ratio identities by reflection. Jacquet's
Appendix Lemmas 16.1 and 16.3 obtain the Gamma comparison using duplication
and polynomial shift identities. [Jacquet, *Archimedean Rankin–Selberg Integrals*, pp. 111–116](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf)
