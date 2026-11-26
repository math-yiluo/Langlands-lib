# Eventual square comparison for twisted Euler polynomials

`CoherentEulerPolynomialSquareComparisonStatement` compares two smooth
proper geometrically connected schemes of relative dimension `g` over
possibly different fields in a common universe. Let `L` and `L'` be ample
line bundles and let `N` and `N'` be arbitrary line bundles on the respective
schemes. If the squares of the actual Euler characteristics of
`N ⊗ L^n` and `N' ⊗ L'^n` agree for every sufficiently large natural `n`,
the two canonical `coherentEulerPolynomial` values in `ℚ[X]` agree.
The equality of squares concerns `coherentEulerSequence`, using actual
cohomology and the finite affine sections hypotheses for line bundles.

This comparison follows from the evaluation and top coefficient formulas
in `MumfordTraceReduction.euler_facts`, uniqueness of a polynomial from
eventual agreement on the naturals, and positivity of the top coefficient
for the ample twisting bundles by `lineBundleEulerPolynomial_topCoeff_pos`.
The intended graph application takes `N` and `N'` to be pullbacks of the ample
bundles along actual endomorphisms. There `Rosati.mumfordEulerDegree`
relates the squared sequences to ranks of actual isogenies.
