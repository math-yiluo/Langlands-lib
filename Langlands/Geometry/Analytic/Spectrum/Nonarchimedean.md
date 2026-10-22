# Proof of the strong triangle inequality for spectrum seminorms

Author: Worker 36.

`Langlands.Analytic.spectrumNonarchimedean` proves the separate proposition
`Langlands.Analytic.SpectrumNonarchimedeanStatement`. The module preserves
the reusable declarations `seminorm_nonarchimedean_of_natCast` and
`BanachSpectrum.isNonarchimedean`, extracted from the residue-field draft.

The private finite-sum lemma iterates the ordinary seminorm triangle
inequality. Given p(n) ≤ 1 on natural-number casts, binomial expansion and
multiplicativity bound p(a + b)^n by (n + 1)M^n, where
M = max(p(a), p(b)). If M is zero, the case n = 1 proves the result.
Otherwise, for each r > M, exponential growth supplies n with
n + 1 < (r/M)^n. This n is nonzero. Comparing powers then gives
p(a + b) ≤ r, and order density yields p(a + b) ≤ M. No division in the
source ring and no nondegeneracy of p is used.

For a spectrum point x of an algebra over an ultrametric normed field K,
the previously proved scalar-normalization theorem identifies
x(n) with the norm of n in K. Mathlib's ultrametric natural-number norm
bound makes this at most one. Applying the general seminorm criterion
proves the second clause. The closing theorem combines both arguments
with the exact statement's independent universes and hypotheses.

The binomial and growth argument adapts the pinned Mathlib proof in
`Analysis/Normed/Field/Ultra.lean` to seminorms on commutative rings.
The statement Markdown records the source context and derived provenance.
This is a prerequisite for converting a spectrum seminorm to a valuation;
it does not construct or assume a completed residue field.
