# Irreducible reduction in the actual common closure

Worker 1727 derives this comparison from the published local irreducible
reduction and the published topological group equivalence
`intermediateWeilEquiv`. No new arithmetic classification premise is introduced.
The field and representation-carrier universes remain independent.

`toIntermediateLocalWeil` is the inverse of `intermediateWeilEquiv`,
bundled as a continuous multiplicative homomorphism. Its domain is the
actual fixing subgroup in the specified closure, with its prescribed topology.

Surjective restriction has the same image in the endomorphisms of the
original vector space, so its lattice of invariant subspaces agrees with
the original lattice. The existing range-equality order isomorphism
therefore transports irreducibility, including nontriviality.

For the prescribed finite intermediate field `E`, pull the actual
continuous irreducible representation back through `intermediateWeilEquiv`
to the standalone local Weil group of `E.asPadicField`. Apply
`localWeilIrreducibleReductionFor` there, then precompose the resulting
finite-image representation and continuous unramified character with the
inverse equivalence. Precomposition preserves continuity and finite
image. The same linear equivalence intertwines the original action with
the resulting character twist, since the group equivalence and its inverse
compose to the identity.

The character in the conclusion is an actual continuous character of the
specified fixing subgroup. This module does not claim finite Brauer
induction or the final exact degree-zero generation statement. Its
provenance is internal transport of the already published arithmetic result.
