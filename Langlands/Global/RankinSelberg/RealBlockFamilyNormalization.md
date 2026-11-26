# Normalization by real block factors in a holomorphic family

`RealBlockFamilyNormalizationStatement` takes two parametrized real block
lists with fixed parities and weights, and exponent maps holomorphic on
the complex plane in the parameter \(z\). The supplied function \(F(z,s)\) is
jointly holomorphic on the parameter disk times the spectral plane and
agrees with the ordinary integral multiplied by the expanded denominator
on a right half-plane for each \(z\).

For imaginary \(z\) in the disk the statement also assumes that the
ordinary and dual integral functions are holomorphic for
\(\operatorname{Re}s>0\) and satisfy `ContinuationPackage` with the primal
and dual block \(L\)-factors and the block epsilon factor at the supplied
additive parameter and positive scale. The functional equation multiplies
the epsilon factor by the same fixed nonzero complex scalar on every
imaginary slice. The conclusion supplies an
`OrdinaryIntegralNormalization` by the block \(L\)-factor for every
parameter in the disk.

The polynomial comparison expresses the ratio of the expanded and block
denominators using a finite list of moving roots. Each root is the negative
of the sum of the two exponents and the corresponding fixed shift.
`realOverlappingNormalization` gives an entire block normalization on
each imaginary parameter slice. Its product with the comparison
polynomial agrees with \(F\) on a right half-plane, so the spectral identity
theorem gives equality on that whole slice. The imaginary parameters
accumulate to zero, so `movingRootDivision` gives joint holomorphic division,
including at the moving roots and their coincidences. On a right half-plane
the two reciprocal pair factors are nonzero and cancellation gives the
defining equality for the resulting ordinary normalization.

This is the analytic passage from expanded to block factors in H. Jacquet,
*Archimedean Rankin–Selberg Integrals* (2009), Proposition 11.1, author p. 82.
The proof uses holomorphic division of the principal-series normalizations
in place of an identity of integrals against Mellin pairs. The joint
expanded continuation and the two half-plane holomorphy statements used
in this passage are hypotheses.
[Registered author edition](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf)
