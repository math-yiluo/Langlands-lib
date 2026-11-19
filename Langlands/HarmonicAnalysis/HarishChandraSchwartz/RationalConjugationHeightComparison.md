# Compact height comparisons for the conjugation integral

The compact envelope of the given matrix height is exactly bi-invariant under
the specified compact subgroup. The two heights with one added bound each
other by a common multiple. Their real powers therefore bound each other by
the same multiple raised to the absolute value of the exponent.

`ConjugationComplementIntegralBound` expresses the absolute-integral bound on
the family of regions complementary to the cells in the conjugation argument.
For inequality (2) in Waldspurger VIII.3.1, compact height comparison bounds
the left side by a multiple of the original expression, and domination of the
original height by the envelope controls the two heights on the right.
`rationalConjugationComplementIntegralBound_of_compactHeight` transports
Schwartz seminorm finiteness and the Xi upper bound to the envelope and applies
`ConvolutionWeights.lintegral_conj_mul_le`. The real-power comparison returns
its final right-hand side to the original matrix height.

`ConstantTermEstimate.rationalCompactHeight_output` applies the power
comparison on the Levi to the output weight of a supplied constant-term
estimate. This is the restriction of the ambient envelope, which is
bi-invariant under the intersection of the ambient compact subgroup with the
Levi. The unipotent integral keeps the original matrix height at its original
exponent, so the same matrix height can be used for the product estimate and
the tail cutoff.

These are derived comparisons from the compact height envelope, the existing
averaging inequality and real-power monotonicity. Their source context is
Waldspurger's 2003 Plancherel article, VIII.3.1, printed pp. 323–326. The
complement estimate takes the geometric height inequality, the Xi upper bound
and convolution weights as hypotheses. The averaging step uses an s-finite,
left and right invariant measure and finiteness of the two functions'
Schwartz seminorms. The constant-term comparison uses the original
constant-term estimate and nonnegativity of the Levi Xi function.
