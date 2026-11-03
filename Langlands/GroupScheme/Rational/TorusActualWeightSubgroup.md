# Actual coordinate weight subgroups

This internal construction specializes the coordinate weight subgroup to the
original automorphic action and actual character lattice, retaining the original
coordinate algebra and augmentation. The field and all schemes have arbitrary
universe `u`. The ambient group is affine; smoothness and connectedness are not
assumed. A chosen isomorphism identifies the acting commutative group scheme with
a split torus indexed by a finite type `I`.

For a corepresented algebra functor, weight-subgroup membership is equivalent
to equality with augmentation on every homogeneous function outside the
semigroup. It is enough to test homogeneous functions of augmentation zero:
subtracting the augmentation preserves homogeneity, since the augmentation of
a nonzero-weight homogeneous function is zero.

The actual character semigroup pulls back along the chosen split-torus
character equivalence. The resulting subgroup on every coefficient algebra is
therefore characterized by actual character eigenfunctions, or by vanishing of
the original augmentation eigenfunctions outside the character semigroup.
Every actual acting point preserves these subgroups. The published coordinate
quotient construction gives a closed group-scheme inclusion into the original
group, using its canonical coordinate model isomorphism.

More precisely, `exponentSemigroup` takes the inverse image of the given actual
character semigroup along `PointedCoordinateWeights.characterEquiv`.
`weightGroupScheme` is the existing group scheme cut out by the corresponding
coordinate weight ideal, and `weightHom` composes its closed inclusion with the
coordinate model isomorphism. There is no restriction on the semigroup: it may
be empty or contain zero.

The affinization lemmas work over an arbitrary commutative base ring and any
affine group. The underlying maps of the recovered group-scheme isomorphism
are the original coordinate isomorphism and its inverse. Consequently the
corepresented all-test point equivalence, applied after the inverse model
isomorphism, is exactly `Lie.affinizationFactor`. Precomposition with the
relative affinization unit is injective on maps to an affine group, by the
relative global-sections/spectrum adjunction and full faithfulness of relative
spectrum. Naturality of the original action and the factorization identity
then show that affinization commutes with any action between affine groups.

For every scheme `T` over the field, `mem_range_weightHom_iff` identifies the
range of the actual inclusion with membership in the algebra weight subgroup
over the relative global sections of `T`. Its proof transports the existing
all-test quotient-range criterion along the coordinate model isomorphism.
The acting split torus is affine, so affinization of an acting point is
available. The action compatibility and the algebra-point stability proved
above yield `isStable_range_weightHom` on every scheme test.

All content is derived internally from the published coordinate quotient,
corepresented point equivalence, split-torus character comparison, actual
action laws, and relative affine adjunction. No external literature theorem
is used. This contribution does not assert that the quotient is smooth or
connected, compute its Lie image, identify its identity component or the
generated semigroup functor, or prove the full semigroup realization target.
