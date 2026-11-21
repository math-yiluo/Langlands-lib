# Real Fourier transform of a separated last-column test

`RealJacquet.realColumnProduct F f` is the Schwartz test on real
`m × (m+1)` matrices (`m = r+1`) taking `[A | x]` to `F A * f x`, where
`F` is a square-matrix test and `f` a row-coordinate test. The linear
projections onto the leading square and last column jointly control the
matrix norm: write the matrix as the sum of the two inclusions with the
other coordinates zero, then use their operator norms. The generic
Schwartz product lemma therefore applies.

The proof of `realColumnProduct_fourier` splits off the last coordinate of
each matrix row and transposes the two finite products of measures. This
is a measure-preserving equivalence from the given product self-dual
measure to the product of the row and square self-dual measures, with no
additional constant. The coordinate pairing is the sum of the two
pairings, so the additive phase is the product of their phases. The
integral of this separated product factors into the two Fourier integrals.
The proof identifies these with the Library's positive rectangular and
row Schwartz Fourier transforms for the **same** parameter `a`.

This is an internal adaptation of the separated-column construction in
`ComplexGodementColumnProduct`. It supplies the full Fourier factorization
for the real tests of Jacquet §8.3 (8.4); it does not use a Whittaker
coefficient or assert its functional equation.
