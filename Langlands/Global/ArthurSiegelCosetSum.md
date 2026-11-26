# Decay of sums over distinct rational translates

`SiegelCosetSumDecayStatement` gives a way to sum estimates over rational
cosets. An injection assigns distinct rational representatives `γ j` to the
indices. For a fixed point `x`, the statement assumes that its height is at
most `C` times the height of each `γ j · x`. Given a desired decay exponent
`n`, the theorem chooses a termwise exponent `m` and a constant before the
point, the representatives and the summands. A uniform bound `B` on the term
norm times the translate height to the power `m` implies absolute convergence
and bounds the sum norm times the height of `x` to the power `n` by a constant
times `B`.

The statement takes an exponent `d` for which the inverse `d`-th power of
adelic height is summable on the rational group. Write `H` for the normalized
adelic matrix height and set `y = γ j · x`. Submultiplicativity and inverse
symmetry give `H(γ j) ≤ H(y) H(x)`. Combining this with `H(x) ≤ C H(y)` gives

\[
H(\gamma j)^d H(x)^n \le C^{d+n} H(y)^{2d+n}.
\]

Taking `m = 2d+n` bounds every summand by a multiple of `H(γ j)^{-d}`.
Injectivity bounds the sum of these weights by the full rational-group sum.
The estimate then follows from the triangle inequality for absolutely
convergent sums.

This is a summability argument for the last step of Arthur's truncation
decay proof. Arthur 1980, Lemma 1.4, pp. 96–97, uses norm minimality on the
testing Siegel set and a polynomial bound for the number of contributing
cosets. The proof here uses the same norm comparison and a convergent majorant
on the representatives.
