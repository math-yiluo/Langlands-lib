# Closed normalizers with projective coordinates

This development extends the Library's normalizer construction using projective
coordinate modules. It is an internal consequence of
`NormalizerRepresentability`, the affine global-section comparison and the
freeness of the group algebra of a diagonalizable group.

`normalizer_hasClosedRepresentative_of_projective` works over any commutative
ring. For an affine ambient group and a closed subgroup whose relative
global-section module is projective, it gives a closed group scheme representing
the normalizer on every scheme test. It identifies the original subgroup with
the subgroup cut out by its defining ideal and transports projectivity to the
coordinate quotient, then applies the existing coefficient-ideal construction.

`diagonalizableNormalizer_hasClosedRepresentative_overRing` specializes this to
any diagonalizable group: its coordinate module is the free group algebra.
Neither a smoothness nor a finite-generation hypothesis on its character group
is needed for this closed representability assertion.

`Diagonalizable.normalizerGroupScheme` and `Diagonalizable.normalizerHom`
choose the actual normalizer group and its inclusion into the original group.
`Diagonalizable.normalizerHom_spec` proves that this inclusion is closed and
represents the normalizer functor on every test scheme.

The intended general-base application is the closed representability part of
Brian Conrad, *Reductive group schemes* (2014), Proposition 2.1.2, p.56, and
Theorem 2.3.1, p.67. The implemented proof uses projective coordinates rather
than Conrad's reduction to finite torsion subgroups.
