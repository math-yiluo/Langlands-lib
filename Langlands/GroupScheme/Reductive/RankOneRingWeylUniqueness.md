# Uniqueness of the rank-one Weyl normalization

This internal derivation assumes actual `RingRootCell.WeylData R` over
an arbitrary commutative ring, with affine ambient group. The unscaled
Weyl product is `B(-1) A(1) B(-1)`.

The quotient of this product by the normalized product `N` is
`B(beta - 1) A(beta⁻¹ - 1)`. Indeed the unscaled product factors as
`B(beta - 1) N B(beta - 1)`, and the negative-root conjugation law for `N`
computes the quotient.

If the unscaled product acts on the torus by the prescribed reflection,
and the torus centralizer equals its image, the quotient centralizes the
torus and hence is a torus point. Uniqueness of the open-cell coordinates
then gives `beta - 1 = 0`. This proves beta is one without a
characteristic or reducedness assumption.

The hypotheses include supplied actual Weyl data and self-centralization.
Constructing those data and proving the full local Isomorphism Theorem
remain separate obligations.
