# Exact normalized equal-rank inputs from canonical Jacquet values

At one rank, assume `HasCanonicalEqualNormalization` for the standard trace character, all inducing lists given by weights and exponents, and all Schwartz row tests. `complexEqualNormalizedFromCanonical` supplies the entire-normalized equal-rank induction input for the full exact Whittaker models and every nonzero character parameter.

Every inducing list has an exact weight and exponent presentation. Multiplicity one writes each Whittaker vector as a canonical evaluation, so the assumed normalization applies to both vectors. The constant inducing lines in `complexLocalEqualCanonicalFamily` supply a common right half-plane of absolute convergence for the same vectors. The normalized character change then gives the result for arbitrary trace-character parameter.

This connects the canonical chamber proof to the normalized input required by the adjacent-rank step. [Jacquet, *Archimedean Rankin–Selberg integrals*, Section 8](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf).

`complexLocalEqualPairConvergence` exposes the two absolute convergence clauses for every pair of exact equal-rank model values and every character parameter. It uses the exact model range and the joint family theorem on a pair of constant inducing lines. The normalization transfer uses this convergence result as well.
