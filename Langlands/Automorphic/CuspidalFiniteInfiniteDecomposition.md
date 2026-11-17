# Finite versus infinite decomposition of cuspidal realizations

This internal construction for Task 7294 derives an actual finite factor from
the existing irreducible admissible finite-slice existence theorem. It uses the
tensor evaluation construction in `FiniteInfiniteMultiplicity` and does not
assert a decomposition into individual archimedean places or construct an
invariant bilinear pairing.

Evaluation at a nonzero vector of an irreducible finite factor is injective on
the space of finite intertwiners: a map vanishing at that vector cannot be
injective, and irreducible Schur forces it to be zero. Evaluation also
intertwines the compact actions. Since all vectors of the actual realization
are compact finite, injectivity transfers compact finiteness to every
multiplicity vector. The compact and genuine enveloping actions satisfy the
existing adjoint covariance, by evaluating on each finite-factor vector.

For every actual cuspidal realization over a number field in an arbitrary
universe, under the existing `CompactSpace (AdeleQuotient F)` hypothesis,
`finiteInfiniteDecomposition` chooses a published nonzero irreducible
admissible finite slice. Its inclusion into the realization's finite image,
followed by the inverse finite-image equivalence, is an injective finite
intertwiner into the actual carrier. Its range is the chosen internal finite
factor. The range equivalence transports irreducibility and admissibility,
and injectivity preserves nonzeroness.

`FiniteInfiniteDecomposition` retains that actual subrepresentation and its
three properties. Its `InfiniteSpace` is the full space of finite intertwiners
from the factor into the original realization. Its tensor equivalence is the
existing evaluation equivalence, sending `a ⊗ f` to `f a` in the original
actual carrier. Its finite, compact and enveloping covariance is supplied by
the imported evaluation identities.
