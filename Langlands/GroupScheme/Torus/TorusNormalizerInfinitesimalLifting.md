# Square-zero lifting for torus normalizers

`HomScheme.hasAffineSquareZeroLifting_of_splitTorusNormalizer` takes a
closed split torus in a smooth group scheme and a homomorphism representing
its full normalizer on every test scheme. It proves square-zero lifting for
the structure morphism of that representative from an explicit proof of
`HomScheme.SquareZeroHomomorphismCohomologyStatement`.

Over an affine square-zero quotient, the given normalizer point conjugates
the original torus embedding to its composite with a torus automorphism.
The reduced split torus is diagonalizable, so its regular cohomology
vanishes in degrees one and two. Apply the bridge to the split torus as
source and target. Its commutative target makes conjugation trivial, so
restriction is injective as well as surjective. Lift the automorphism and
its inverse and check their inverse identities after restriction.

Apply the bridge again to the original embedding and its composite with
the lifted automorphism. It lifts the prescribed conjugating point in the
ambient group. The lifted automorphism implies that the point belongs to
the normalizer, and the monomorphic representing inclusion identifies its
restriction with the original point of the normalizer scheme.

`relativeTorusNormalizer_smooth_of_squareZeroCohomology` applies the scheme
smoothness criterion when the representing group's structure morphism is
locally of finite presentation, and descends smoothness along an étale
splitting cover of the torus.
`relativeTorusSmoothNormalizerModel_of_squareZeroCohomology` uses the
locally finitely presented closed normalizer to supply that premise and
returns an actual smooth closed representative.

This is an internal composition of the Library's source-automorphism
description of normalizer points, diagonalizable cohomology vanishing,
and the two scheme-level normalizer constructions. The cohomology bridge
is a proof input throughout.
