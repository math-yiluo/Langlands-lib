# Actual-root blocks for ordered semigroup products

This is an internal combinatorial adapter for the existing ordered-product
target. It defines `rootRayBlock i a` as the intersection of the actual relative
roots with the first positive cyclic tail through `a`. It does not prove the
relative-root ray decomposition or any group-scheme realization or product
isomorphism.

If `a` is an actual root, it belongs to its block, and positive repeated
addition shows that the block generates the entire positive cyclic semigroup.
Conversely, that semigroup already contains every block element, so minimality
of additive semigroup closure gives `closure_rootRayBlock`. Zero is not inserted
by this argument.

A ray whose initial character pairs positively with a cocharacter remains in
the strict positive halfspace, by positivity of positive integer multiples.
Consequently the block of an indivisible positive root consists of positive
actual roots. Given the precise ray-cover conclusion of
`RelativeRootRayDecompositionStatement`, any enumeration of its indexing set
has block union equal to `positiveRelativeRoots`. This proof works for an empty
index set and makes no genericity assumption.

`rootRayBlock_pairwise` uses injectivity of the given enumeration and the
explicit disjoint-ray conclusion to obtain pairwise disjoint blocks. Replacing
the closure of the second block by its full cyclic tail gives exactly the
cross-exclusion condition from `SemigroupOrderedProductStatement`. It does not
assume or prove a stronger condition on arbitrary generated weight blocks.

The provenance is internal: these are set and additive-semigroup consequences
of the definitions and explicit hypotheses imported from
`Rational.RootProductStatement`. Their intended role is to adapt the separately
owned ray-decomposition theorem to the CGP ordered-product interface. No
additional source assertion is introduced here.
