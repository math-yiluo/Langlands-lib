# Closed normalizers of subgroups of multiplicative type

This derived module extends the projective-coordinate construction in
[`DiagonalizableNormalizer`](DiagonalizableNormalizer.md) to arbitrary base
schemes by fppf descent. It supplies the closed-normalizer assertion required
by `RelativeMultiplicativeTypeQuotientStatement`. It does not supply quotients.

For every scheme `S`, relatively affine group scheme `G` over `S`, group
scheme `H` of multiplicative type, and closed subgroup homomorphism
`i : H ⟶ G`, the theorem
`relativeMultiplicativeTypeNormalizer_hasClosedRepresentative` gives a closed
subgroup scheme representing `(SubgroupFunctor.range i).normalizer` on
every relative test scheme and every refinement. If `H` is a commutative group
scheme, this is exactly `torusNormalizer i`. Smoothness of `G` is not required.
The multiplicative-type hypothesis uses the published relative definition:
an fppf cover locally identifies `H` with a diagonalizable group attached to
a finitely generated abelian group, allowing torsion and nonsmooth subgroups.

The proof first establishes that the normalizer of a monomorphically
represented subgroup agrees with the all-test condition descended from its
base changes on any fppf cover. Both conjugation conditions descend because
membership in the represented subgroup is fppf local on each test scheme.
The local base changes satisfy the matching condition by restriction.
`CoverDescent.isClosedRepresentable_subgroup_fppf` therefore descends closed
normalizer representatives.

On an affine base `Spec R`, the diagonalizable comparison
`Diagonalizable.baseChangeIso` identifies the published relative
diagonalizable group with `Spec R[M]`. Precomposition with this group
isomorphism preserves the range and closedness of `i`, so the ring-level
projective-coordinate normalizer theorem applies. The affine open cover
gives the diagonalizable case over an arbitrary base. The defining fppf
splitting cover then gives the multiplicative-type case.

`RelativeMultiplicativeType.normalizerGroupScheme` chooses this representative,
`normalizerHom` chooses its inclusion, and `normalizerHom_spec` records
closedness and the complete representing property for these same choices.

The intended original-source application is Brian Conrad, *Reductive group
schemes* (2014), Proposition 2.1.2 (pp.56–58) and Theorem 2.3.1 (pp.67–69),
registered as `conrad-2014-reductive-group-schemes`. This module is an internal
derivation from published coordinate representability, diagonalizable
base change, represented membership locality and closed-locus descent.
It does not assert finite presentation, smoothness of the normalizer,
or any of the quotient conclusions of Theorem 2.3.1.
