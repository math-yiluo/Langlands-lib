# Full Galois and star covariance of actual root-factor placement

This module is derived interface material for realizing the Cartan components
of a semisimple Tits index by actual simply connected factors, using the
published full root-datum star action, actual all-test root subgroups, and
canonical Galois transport of actual almost-simple normal product factors.
It cites no additional external result.

For a split maximal torus of a semisimple group with an actual simply connected
almost-simple product presentation, `rootDatumFactorIndex_reflection` proves that
all abstract root reflections preserve the assigned actual factor.
`rootDatumFactorIndex_weyl` extends this to every element of the full root-datum
Weyl group, without a condition on the chosen base. A nonzero ordered pairing
forces both roots into the same factor by the cross-factor vanishing theorem;
if that pairing is zero, its reflection fixes the root. These two cases prove
the reflection assertion and Weyl group induction proves the general assertion.

For actual Galois pinning data over any extension, `rootDatumFactorIndex_galois`
compares the ordinary root-index Galois action with `galoisFactorIndex`.
Canonical coefficient transport preserves all-test subgroup inclusion and takes
the root subgroup exactly to the subgroup of its actual transported character.
Uniqueness of root-factor placement identifies its translated factor.
`rootDatumFactorIndex_star` removes the full Weyl correction by the preceding
invariance theorem. Smoothness of the base-changed group is an explicit instance
needed by the existing canonical factor-index API; it is provided by the
semisimplicity hypothesis.

For an actual Tits index, `geometricFactorIndex` assigns each simple vertex its
actual geometric normal factor. `geometricFactorIndex_eq_of_cartanConnected`
is constant on the entire Cartan component, while `geometricFactorIndex_star`
intertwines every element of the full absolute Galois group.
`cartanComponentStabilizer_le_factorStabilizer` proves subgroup containment.
`cartanComponentStabilizer_eq_factorStabilizer` gives equality of the full
subgroups conditional on the explicitly supplied reverse component
identification. This module does not claim that reverse identification.

The constructions are at every universe parameter `u`, over arbitrary fields;
no characteristic, perfectness, local-field, or classification hypothesis is used.
