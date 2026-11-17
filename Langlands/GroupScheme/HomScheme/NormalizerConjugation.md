# Normalizer points as source automorphisms of conjugation families

Let `i : H.toGrp → G` be a homomorphism from a commutative group scheme whose
underlying scheme map is a monomorphism, over any scheme `S`. For every
`T : Over S` and `g : T → G`, `exists_sourceIso_conjugationFamily_iff` proves:
the conjugation family of `i` by `g` is the constant base-changed embedding
precomposed by a source automorphism if and only if `g` belongs to the full
all-refinement normalizer of `i`.

`normalizerSourceIso` chooses that actual source automorphism for a supplied
normalizer point and retains the equality with the conjugation family.
There are no smoothness, affineness, finite-presentation, or multiplicative-type
hypotheses here.

The proof transports normalizer membership to the base point of `G_T` by
normalizer base change and the pulled-back-point equivalence. It then applies
the published equivalence between normalizer-functor points and points admitting
an actual automorphism of the monomorphically represented source. The
commutative-group and group-scheme isomorphisms are converted through their
underlying morphisms. Membership is explicitly transported between `T` and
`Over.mk T.hom`, rather than assuming these slice objects are definitionally
equal.

This is an internal derivation from the imported normalizer and conjugation-family
APIs. The comparison of two different conjugation families and the quasi-affine
normalizer quotient are separate steps.
