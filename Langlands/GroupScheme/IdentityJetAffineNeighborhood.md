# Smoothness and rank along the unit in affine coordinates

An affine open immersion into the total scheme of a separated group contains
the unit if the actual unit factors through it. Over an affine base,
`neighborhoodAugmentation` evaluates at that factorization.
`neighborhoodJetAlgEquiv` identifies the algebra of the actual identity jet
with the quotient by the corresponding power of the augmentation ideal.

`SmoothAlongUnit` requires formal smoothness of the actual stalk map at
each point of the unit. `SmoothAlongUnitOfRank` also requires the actual
first-jet projection to be flat and its rank at every base point to be
`1 + r`.

For a separated locally finitely presented group, the two affine
recognition theorems identify the unit stalk condition with formal
smoothness of the neighborhood algebra localized at the section primes.
Local finite presentation gives geometric smoothness at those points.
The fixed-rank theorem identifies the additional first-jet tests with
conormal dimension `r` over each base residue field. The first-jet splitting
has scalar and conormal summands, and smoothness along the section makes
the conormal projective. This supplies flatness of the first jet and gives
relative dimension `r` at the section.

This comparison applies Raynaud's smooth-section conditions in SGA 3,
Exposé XV, Lemma 5.4 to an affine unit neighborhood of an actual group.
