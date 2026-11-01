# Assembly of the actual smooth proper Euler polynomial theorem

`smoothProperLineBundleEulerPolynomial` proves the unchanged
`SmoothProperLineBundleEulerPolynomialStatement` in arbitrary universe `u`.
For a smooth proper geometrically connected scheme of relative dimension `g`
over any field, it supplies finite cohomology for every nonnegative tensor
power of an actual line bundle and a rational polynomial evaluating to its
actual integer Euler characteristics. The polynomial has degree at most `g`;
for an ample bundle its degree is exactly `g` and its leading coefficient is
strictly positive.

This is an assembly of published Library constructions and proofs. Its
provenance is the derived specialization documented in the paired target
statement; it introduces no additional geometric hypothesis or numerical
certificate. The implemented proof proceeds as follows.

Properness and smoothness over the field supply the Noetherian and separated
instances needed by the actual coherent-cohomology constructions. The
polynomial witness is `lineBundleEulerPolynomial X.hom L g`, the prescribed
Newton polynomial at truncation `g`. The finiteness witness is
`lineBundleTensorPow_hasFiniteCohomology X.hom L`, which concerns the actual
derived cohomology of every tensor power. The published theorem
`smoothProperConnectedFiniteFlatGeometry`, applied to the identity
endomorphism, gives exact topological Krull dimension `g`. This supplies the
dimension bound for `lineBundleEulerPolynomial_eval` at every natural number,
including zero. The construction's `lineBundleEulerPolynomial_natDegree_le`
supplies the degree upper bound.

For an ample bundle, apply `ampleCoherentEulerCoefficientReduction` to the
proved theorem `coherentIntegralIdealFiltration`, with coefficient module the
actual structure module and dimension `g`. Its support satisfies the strict
bound `g+1` by the topological dimension bound. Its support dimension equals
the full topological dimension, so the strict bound `g` would contradict
irreflexivity of strict order. The coefficient criterion therefore makes the
coefficient of degree `g` strictly positive.

The degree upper bound and this nonzero coefficient give natural degree
exactly `g` by `Polynomial.natDegree_eq_of_le_of_coeff_ne_zero`. Rewriting the
definition of `Polynomial.leadingCoeff` identifies it with the positive
coefficient just obtained. This argument also covers `g = 0`.

All geometric, cohomological, filtration and coefficient inputs are proved
Library results imported by Lean name. The theorem has no outer polynomiality,
positivity or filtration premise.
