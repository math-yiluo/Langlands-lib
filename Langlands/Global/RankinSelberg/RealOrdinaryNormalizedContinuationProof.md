# Ordinary normalized continuation over the real field

`realOrdinaryNormalizedContinuation` proves
`RealOrdinaryNormalizedContinuationStatement`. For each test in
the exact coefficient models of the supplied real block lists,
it gives a function \(N\) analytic on all of \(\mathbb C\) such
that \(Z(s)=N(s)L(s)\) on a right half-plane. Here \(Z\) is the ordinary
local integral with its supplied compatible quotient measure, and \(L\)
is the original pair factor. The two coefficients use opposite
nonzero additive scales. The result covers every unequal-rank
pair and every equal-rank pair with its supplied Schwartz function.
It includes zero tests and gives analyticity at every zero of
the reciprocal pair factor.

The proof applies `realOrdinaryBlockAssembly`.
`realLocalUnequalCharacterGrowth` supplies unequal-rank character
growth. For equal rank the uniform canonical range and standard
evaluation theorems supply the hypotheses of
`realLocalEqualCharacterGrowth_of_canonicalPremises`.
`RealTemperedWhittaker.realTemperedWhittakerBound` supplies the
scalar estimate for every positive rank index.

`realOrdinaryHolomorphicTestFamilies_of_ascending` lifts each given
test to families in the deformation parameter \(z\), with the original
test at \(z=1\). The canonical range produces the families in the
uniform ascending character models. The equality of exact and uniform
models, `realWhittakerModels_eq`, and the ascending comparison,
`realAscendingWhittakerModels_eq`, give membership in the original
block models along the deformation.

The assembly obtains a joint holomorphic continuation after multiplying
the integral by the reciprocal of the expanded character pair \(L\)-factor.
At imaginary parameters the deformed block exponents have zero real
part. There the tempered estimate, coefficient regularity and toral
gauges give convergence and holomorphy of the ordinary and dual
integrals on \(\operatorname{Re}s>0\). The block functional equation
glues the normalizations across \(0<\operatorname{Re}s<1\), where the
ordinary integral at \(s\) and the dual integral at \(1-s\) both
converge. The expanded reciprocal \(L\)-factor equals the block
reciprocal \(L\)-factor times a polynomial in \(s\) with moving roots.
The imaginary slices give divisibility of the continued expanded
normalization by that polynomial. Holomorphic division across the
moving roots and their coincidences gives the joint block normalization.
Its value at \(z=1\) supplies the required entire function. The assembly
uses the rank-one normalization for the equal-rank pair of characters.

This formalizes the ordinary real holomorphic-multiple conclusion of
Jacquet's Theorem 2.1(ii) for formulas (2.4) and (2.6), author pp. 6–7.
The passage from character principal series to real block lists uses the
deformation of Proposition 11.1, author p. 82, implemented by joint
continuation and holomorphic division. The retained author edition is
registered as `jacquet-2009-archimedean-rankin-selberg`, SHA-256
`7a11766eadf25fb7452ce7faa193469791796f572fc654c8fe90a8608bb46afe`.
[H. Jacquet, *Archimedean Rankin–Selberg Integrals* (2009), author edition](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf)
