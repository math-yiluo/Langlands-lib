# Strict normalized Jacquet exponents bound compact compression

Author: Worker 19.

`Langlands.NormalizedJacquetCompressionSpectrumStatement.{uG,uV}` is a
derived internal spectral proposition, with independent group and carrier
universes. It concerns an admissible smooth complex representation `A` of
a locally compact nonarchimedean group `G`, three actual subgroups
`N`, `M`, `Nbar`, a closed `N` normalized by `M`, and a compact open
subgroup `K`. It assumes the published
`Jacquet.HasIwahoriContractionBasis N M Nbar`, which permits deriving
admissibility of the normalized Jacquet module.

For a point `z` of the full center of `M`, it also assumes
`Jacquet.IsIwahoriContraction K N M Nbar z`. If every full-center exponent
of the actual normalized Jacquet module has absolute value less than one
at `z`, then every eigenvalue `μ` of the actual compact compressed action
of `z` satisfies

`‖δ_N(z)^(-1/2) * μ‖ < 1`.

The scalar is literally
`HaarModulus.closedInverseHalfCharacter N hN M hMN z`, the Haar
normalization used by `Aubert.General.normalizedJacquetFunctor`. The
conclusion includes eigenvalue zero. No modulus comparison with a root
product is asserted.

The intended proof sends a nonzero-eigenvalue eigenvector into the actual
Jacquet quotient, using the published compression-kernel equality to
prove its image is nonzero. The normalized quotient action then has
eigenvalue `δ_N(z)^(-1/2) * μ`. Full-center eigenvalue detection supplies a
central exponent to which the strict bound applies.

This isolates a general spectral step in the strict Jacquet criterion.
The contraction basis, the contraction at `z`, and the strict bound are
explicit hypotheses of this helper. It does not assert these geometric
conditions for any reductive group, any coefficient estimate, or square
integrability. Those conditions still have to be proved when using this
helper in the complete rational-point target.
