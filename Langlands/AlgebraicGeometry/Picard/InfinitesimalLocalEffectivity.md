# Local effectivity for actual infinitesimal Picard gluing data

This internal result combines simultaneous affine trivialization, nilpotence
of the exact restricted sections map, and actual Picard effectivity for
globally trivial legs. It concerns actual line bundles and specified overlap
isomorphisms, rather than their isomorphism classes.

`EffectiveAffineNeighborhood` records an affine neighborhood inside a prescribed
open and an actual isomorphism of gluing data from the ordinary comparison
image of the trivial bundle to the exact restricted datum. Restriction uses
`SquareGluingRestriction.toOpen` and retains its ordinary composition
comparisons.

The generic helper `isEffectiveOn_of_frames` constructs the witness on a
specified open from the two module frames and the nilpotent-surjective
global-sections map on its exact right restriction.
`ofSimultaneousNeighborhood` packages that construction with an already
chosen simultaneous affine neighborhood. These helpers apply to any
commuting square of schemes in the common universe.

`affineSquareNeighborhood` constructs such a neighborhood at every point of
the actual base change `X_R`. Here `k` is any commutative ring, `f : X → Spec k`
is arbitrary, the four maps of commutative `k`-algebras form a categorical
pullback square, and `B → C` is surjective with nilpotent kernel. No properness,
field, finiteness or locality assumption is used.

The implemented construction first obtains simultaneous frames for both
inverse-image bundles on an affine neighborhood. The exact right restriction
is surjective on global sections and has nilpotent kernel. Applying
`SquareTrivialEffectivity.trivialObjectIso` to those frames gives the specified
isomorphism for the actual restricted Picard comparison.

The local realization is the conclusion proved here. Gluing these local
objects and proving full faithfulness of the total comparison remain separate
obligations of the host infinitesimal gluing task.
