# Integer Hom coproducts from finite decompositions

This internal construction isolates the preadditive part of the published
finite-factorization argument in `SmallProjectiveFiniteType`. It assumes a
cofan with coordinate projections and finite component decompositions of
every morphism from the chosen object. It requires neither an abelian
category nor a colimit assumption on the original cofan.

The image cofan under the actual `preadditiveCoyonedaInt` functor is a
coproduct of integer modules. A map from its vertex to any target cofan is
the finite sum of the images of its components. The finite-support
hypothesis makes this sum additive. Additivity gives compatibility with the
actual restricted integer actions. The inclusion/projection identities prove
the cofan equations; the finite decomposition proves uniqueness.

The construction retains independent object, morphism and index universes.
It is an internal helper for the actual inertia-block smallness argument,
where abelianness of the block is not assumed.
