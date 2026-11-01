# Algebra of the exact ordered adjacent-rank lower parabolic

This derived algebraic prerequisite fixes the ordered shape `(r+1,1)` of
`AdjacentRankModelImageStatement` without reversing the two inducing factors.
The actual ambient rank is `r+2`, and `r` is any natural number, including zero.

`adjacentRankLowerShape` abbreviates the published `Shahidi.twoBlocks` shape.
`adjacentRankLowerLargeProjection` is the group homomorphism from its actual
opposite parabolic to `GL_(r+1)` selecting the first diagonal block. Its entry
formula identifies that block with the first `r+1` rows and columns. The
opposite-parabolic membership condition forces the last column above the last
entry to vanish. Consequently actual rectangular multiplication satisfies
`[h,0]p = [h a(p),0]`, for every inner general-linear element `h`.

The published `TwoBlockConvergence.determinant_oppositeParabolic` factors the
determinant of an arbitrary opposite block parabolic element into its
diagonal-block determinants over a commutative ring. Specializing that existing
finite product to two blocks yields `adjacentRankLower_determinant`.

All these statements are algebraic. The general determinant factorization
requires only a commutative ring; the adjacent-rank projection and rectangular
identity are supplied over a field in an arbitrary universe. There are no
measure, representation, topology or positive-rank hypotheses beyond the
positive block sizes `r+1` and `1`.

The motivating original is Jacquet–Piatetski-Shapiro–Shalika, *Rankin–Selberg
Convolutions* (1983), Section 6.1, printed p.430, the lower-parabolic covariance
(11) of the compact-orbit construction (10). The block extraction and generic
commutative-ring determinant argument are internal derived content. This unit
provides the literal matrix identities used by that covariance; it does not
construct normalized sections, Jacquet functionals or an image equality.
