# Properties of the actual constant automorphic realization

This internal successor to `ConstantFunctions` proves whole-operator
irreducibility and the trivial central character of the actual embedded
constant line in every natural rank and arbitrary number-field universe.
Under the published explicit compactness hypothesis on the additive adele
quotient, it constructs a rank-one irreducible cuspidal object and its class.

## Irreducibility and the central character

`ConstantFunctions.realization_isIrreducible F n` concerns the published
representation of the entire concrete automorphic operator algebra. Its
carrier is the actual subspace constructed in `ConstantFunctions`, not a
replacement scalar carrier. The preceding scalar equivalence proves its
complex dimension is one. Mathlib's simplicity theorem for a module of
finite dimension one makes its submodule lattice simple. Forgetting a
subrepresentation to its underlying submodule is injective and preserves
bottom and top, which proves that every subrepresentation is bottom or top
and that those two subrepresentations are distinct.

`realization_hasCentralCharacter F n` proves the trivial central character
on that actual embedding. Every vector is a constant under `scalarEquiv`;
evaluation at a scalar-idele translate is unchanged, and the trivial
idele-class character pulls back to one. There is no restriction on `n`,
including zero, and no supplied character-action premise.

## Actual rank-one cuspidal objects

`isCuspidal_rankOne F f` proves the existing `IsCuspidal F 1 f` predicate
for every continuous rational-left-invariant rank-one function. This follows
from the exact definition: a proper standard maximal block parabolic would
require positive natural numbers `a,b` with `a+b=1`. Such a pair does not
exist. This does not evaluate or assume a vanishing integral.

As in the existing cuspidal API, this section requires
`[CompactSpace (AdeleQuotient F)]`. The proof does not construct that
instance. `ConstantFunctions.realization_isCuspidal_rankOne` applies the
rank-one result to every vector of the actual constant realization.
`rankOneCuspidal F : CuspidalOperatorRealization F 0` is then a concrete
object with underlying matrix rank `0+1=1`, the proved irreducibility and
the proved cuspidality. Its central character is trivial.

`rankOneCuspidalClass` is the full-operator isomorphism class of this
constructed object. `rankOneCuspidalClass_toOperatorClass` identifies its
forgetful image with the original actual constant-line operator class.
No existence assertion is used to choose a representative.

## Provenance and scope

All results are internal consequences of the published actual constant-line
construction and the exact definitions in `OperatorRealization` and
`CuspidalOperatorRealization`. The only additional algebra is the pinned
Mathlib dimension-one simplicity theorem and the injectivity of the
subrepresentation-to-submodule map. No new original-literature assertion is
used. This module constructs one actual rank-one cuspidal example; it does
not assert cuspidality of higher-rank constants, a realization of every
Hecke character, a factorization theorem or a spectral decomposition.
