# Primal normalized transfer from compact real parabolic sections

`realCompactParabolicPrimal` uses the nonzero Whittaker evaluations of the
ambient smooth module and its two Levi factors at one additive scale.
If the comparison rank equals the leading rank, every equal-rank
normalization with a compact rectangle's row Fourier profile gives an
ambient unequal-rank normalization. If the comparison rank is smaller,
one fixed compact rectangle test works for every input normalization.
In both cases the ambient normalized value is the original value times
the pair denominator for the trailing block. The measures on the two
integrals are the same supplied compatible quotient measure.

The compact parabolic restriction gives the leading coefficient times
the row profile and the determinant half-power. At equal cut rank this
power cancels the unequal-rank shift to give the equal-rank integrand.
For a smaller comparison rank the last row is fixed by padding, and the
profile chosen to be one there removes the row factor. The integral
identities transfer entire normalizations and multiply their values by
the complementary denominator. The determinant and denominator formulas
use the order of the actual upper-Borel concatenation.

At a fixed spectral point, `exists_compactProfile_eval_ne_zero` detects
any supplied nonzero continuous row evaluation on the dense set of
compact rectangle profiles.

These are the equal and strictly smaller comparison-rank cases of the
primal comparison in the proof of Proposition 14.3, p. 104 of the
author-posted edition of [H. Jacquet, *Archimedean Rankin–Selberg Integrals* (2009)](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf#page=104).
The registered source is `jacquet-2009-archimedean-rankin-selberg`, SHA-256
`7a11766eadf25fb7452ce7faa193469791796f572fc654c8fe90a8608bb46afe`.
