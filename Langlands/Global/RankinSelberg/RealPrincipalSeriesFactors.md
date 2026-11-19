# Pair Gamma multiplier for real principal-series positions

For two real block lists `ds` and `es`, `pairMultiplier` is the scaled epsilon factor
times the primal reciprocal L-factor denominator at `s`, divided by the dual
reciprocal L-factor denominator at `1 - s`. The dual lists consist of the blockwise
inverses of the displayed lists. `PairMultiplierExpansionStatement` says that expanding
both lists into their principal-series positions preserves this multiplier off a
discrete set, for every nonzero real additive parameter and positive Haar scale.

An induced block of absolute weight `k` and exponent `t` expands into two real
characters of exponents `t + k/2` and `t - k/2`, and parities `(k + 1) mod 2` and `0`,
in that order. `realRank_expand` and `realPositionCharacter_expand` preserve the rank
and the inducing character at each position. The dual of an expanded presentation
inverts each position character, preserving the parity at its original position.

The proof first inverts the standard multiplier. In the positive Fourier
convention its standard epsilon phases are powers of `i`, giving powers of `-i`
in the inverse. The character–character case is immediate. Tensoring an induced
block with a character shifts both exponents and adds the character parity at
both positions. The two-character reflection identity then gives the twisted
induced ratio, in either tensor order. For two induced blocks of absolute weights
`m` and `n`, the four-character identity gives factors of weights `m + n` and
`|m - n|`. The absolute values of the sum and difference of the signed weights
give those two weights in either order. The argument includes the weight-zero
factor. Multiplicativity on concatenation and induction on both block lists lift
the comparisons to the tensor presentation. Each auxiliary reciprocal Gamma
denominator is nonzero on the codiscrete filter, so the finite products use a
common domain.

The proof compares the denominator of the pair of inverse lists with the
denominator obtained by inverting each block of the tensor presentation. The
Gamma shifts agree in every tensor case. To restore the scales, the product of
the position characters at a real unit gives the determinant of the original
block. For an induced block the opposite exponent shifts cancel and the power
of the real sign agrees with the sign times the restricted complex character.
The pair tensor rank and determinant formulas now give the same scaling term
for the two presentations. Inverting the ratio equality and multiplying by
that term proves `pairMultiplier_expand`.

This is the factor comparison in the principal-series step of Task 7400. The
argument uses reflection to establish the meromorphic Gamma comparison of
Jacquet's §11 and Appendix Lemmas 16.1 and 16.3. Application to local integrals
still requires Whittaker model inclusion and the principal-series equations.
The global reduction also requires the actual contragredient denominator
comparison. [Jacquet, *Archimedean Rankin–Selberg Integrals*, pp. 81–82 and 111–116](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf)
