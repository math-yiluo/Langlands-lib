# Quasi-affine centralizer quotients over a ring

This internal derivation transports the coefficient orbit in
`CentralizerAffineOrbit` through the actual affine coordinate isomorphism.
Projectivity of the closed subgroup's relative global sections transfers
to the quotient coordinate algebra by the isomorphism with its cut-out model.
Consequently an affine parameter map exists with exactly the full centralizer
cosets as fibers on every scheme test.

For a smooth affine ambient group and any smooth closed representative of
this centralizer, `RelativeQuasiAffineHomogeneousQuotient` constructs an actual
homogeneous quotient that is smooth and quasi-affine over every affine open
of the base.

For a closed diagonalizable subgroup over a ring, its group-algebra coordinates
are free, so the projectivity premise holds. The smooth closed centralizer
model is supplied by `RelativeCentralizerSmooth`. Every other representative
is isomorphic to this model compatibly with its inclusion, so it is also
smooth and closed. The preceding construction therefore supplies the quotient
for every representative. The character group is arbitrary; torsion and
nonsmooth diagonalizable subgroups are permitted.

`diagonalizableCentralizerQuotientOverRing` chooses this actual homogeneous
quotient and retains its smoothness and quasi-affineness properties in a subtype.
The quotient carries the projection and homogeneous-space properties required by
`HomogeneousQuotientFromEmbedding.HomogeneousQuotient`.

This module is confined to a base of the form `Spec R`. It does not yet
descend these quotient schemes to a general base or construct normalizer
quotients.
