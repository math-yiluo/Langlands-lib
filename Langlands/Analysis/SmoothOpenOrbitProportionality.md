# Proportionality of covariant functionals on a free open orbit

Let a locally compact group act linearly on a finite-dimensional real space,
continuously in the operator norm, and suppose the orbit map of a base point
is a homeomorphism onto an open subset. Two continuous complex-linear
functionals on the smooth compact tests of that subset that transform by the
same continuous character are proportional whenever the first is nonzero.
This is `SmoothOpenOrbitProportionalityStatement`.

Choose a nonnegative smooth bump supported in the orbit and equal to one at
the base point. Integrating its inverse translates against left Haar measure
gives the same positive mass at each point of the orbit. For a test \(f\),
the family formed by multiplying \(f\) by these inverse translates has one
compact spatial support. Only a compact set of group parameters can contribute
because the two compact spatial supports lift to compact sets under the orbit
homeomorphism. All spatial derivatives vary continuously with the parameter.
The test-family integration theorem therefore moves the integral through the
functional.

Covariance transfers the group action from the bump to \(f\) with the specified
character weight. The resulting test is the fixed bump times the weighted
integral of translates of \(f\). The modular change of variables expresses that
weighted integral at any orbit point as its value at the base point times a
factor depending only on the point and the character. Hence the transformed
tests all lie on a single line, and the original functional values are obtained
by division by the positive bump mass. A test on which the first functional is
nonzero fixes the ratio for every other test.

This is an internal generalization of the compact-family averaging argument
in `LongestBruhatCellInvariance`, applied to the free orbit of the whole Borel
and the upper unipotent on the real reversal cell.

`exists_ne_zero_smul_orbitIntegral_of_covariance` gives the scalar relative to the explicit character-weighted Haar integral evaluated at the base point. The cutoff comparison expresses each test value as the ratio of its orbit integral to that of one test of nonzero functional value, times that test value. The same comparison proves that the denominator is nonzero. Applying this formula to two nonzero functionals proves their proportionality.
