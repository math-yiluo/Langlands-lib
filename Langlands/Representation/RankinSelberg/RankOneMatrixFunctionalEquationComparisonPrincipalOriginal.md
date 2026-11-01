# Actual original comparison for the uniform principal realization

This is an internal derivation from the published uniform principal extraction,
its spectral weighting, and the actual normalized left-average realization.
It retains the original model vector, test and prescribed extraction constant.
The field and representation spaces have independent universe levels.

For a positive level `a` with `conductor(ψ)+a ≥ 0`, the test is exactly
`boxLatticeTest F (conductor(ψ)+a) (conductor(ψ)) a`. If the original model
vector is right fixed by that principal subgroup, `principalOriginal_value`
identifies its convergent shifted matrix integral with
`boxExtractionConstant` times its original rank-one model integral.
The proof applies the forward weighted extraction theorem, evaluates the
compact principal average using the right stabilizer, and uses the existing
`glOneMeasure` density to turn the shifted determinant exponent into the
rank-one exponent. No identification of arbitrary compact averages with the
original vector is used.

`PrincipalOriginalAssertions` records a common right half-plane of genuine
raw original matrix convergence and the comparison for the specified actual
bi-smooth coefficient `averagedModelCoefficient`. The theorem
`principalOriginalAssertions_of_realization` derives it from the matrix
convergence assertion and `PrincipalModelRealization`: pointwise equality on
the box makes the two entire matrix integrands equal, so convergence transfers
before the integral is evaluated. The scalar is exactly the positive
`boxExtractionConstant` supplied by the same uniform box.

The auxiliary `compactOpen_matrixTest_fourier_invariant` works for any supplied
compact open subgroup fixing the original full-matrix test. Published actual
Fourier covariance implies that its inverse-transpose subgroup fixes every
Fourier partner. Compactness gives determinant norm one there. This applies
to the subgroup chosen by `PrincipalModelRealization`, without replacing it by
a separate test-only subgroup.

This contribution proves the original comparison and the stated stabilizer
fact. It does not assert raw inverse-transpose convergence or a complementary
dual comparison.
