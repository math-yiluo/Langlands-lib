# Full upper-unipotent covariance of the scalar Jacquet integral

`Langlands.Whittaker.twoBlockJacquetCovariance` proves the closed published
`TwoBlockJacquetCovarianceStatement` for the actual ordered normalized induction.
It transports initial scalar integrability and gives the positive full standard
character for every upper-unipotent right translate.

The algebraic helpers first prove that a block diagonal matrix with unipotent
blocks is upper unipotent. The two diagonal blocks of an arbitrary full upper
unipotent matrix are upper unipotent as well. Applying the published
`upper_mul_parabolic` calculation at rectangular coordinate zero factors the
matrix as an exchanged diagonal times an exchanged radical. This uses the
exchanged-parabolic API of `TwoBlockCellUnipotentStabilityProof`.

The superdiagonal sum of a block diagonal matrix splits into its two block sums,
because the boundary entry vanishes. Arithmetic rank exchange preserves the
adjacent indices. Consequently the positive standard character on the exchanged
diagonal is the product of the two factor characters.

For the integral theorem, translate the actual induced vector first by the
radical. The published radical covariance formulas preserve integrability and
supply its positive character. The actual inducing covariance theorem applies
to this translated vector, so the diagonal covariance theorem supplies the
product of the factor characters and again preserves integrability. Associativity
identifies the successive right translates with the original full translate.
Multiplicativity of the full standard character, the diagonal character identity
and the definition of the radical character identify the resulting scalar.

This internal proof uses ordinary scalar integrals under the stated initial
integrability hypothesis. It constructs no global integral on the entire induced
representation and does not assert the host extension theorem.
