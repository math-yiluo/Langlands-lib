# Finite support of actual relative roots

This internal auxiliary module proves finiteness of the actual relative-root
set for a homomorphism from a split torus to an affine group scheme locally
of finite type over an arbitrary field. The homomorphism need not be an
embedding, and the ambient group need not be smooth, connected or reductive.
The definitions of roots and weight spaces are the existing actual
adjoint-action constructions.

`IsSplitTorus.finite_weightSupport` combines two published or imported facts.
The actual Lie kernel is finite-dimensional by `Lie.finiteDimensional_lieKernel`,
proved in the paired auxiliary module by evaluation of identity derivations
on finite algebra generators. The published
`isInternal_weightSpace_of_isSplitTorus` makes its character weight spaces
an internal direct sum. These submodules are therefore independent.
Mathlib's `Submodule.finite_ne_bot_of_iSupIndep` says that only finitely many
members of such a family can be nonzero in a Noetherian module, as a
finite-dimensional vector space is.

`IsSplitTorus.finite_relativeRoots` restricts this finite support to the nonzero
characters, exactly as in `relativeRoots`. The positive-root and simple-root
finiteness corollaries then use the published subset inclusions. They allow an
empty simple system and make no reducedness assumption.

`relativeRootFintypeOfIsSplitTorus` and
`simpleRelativeRootFintypeOfIsSplitTorus` use these proved finiteness results
to construct finite enumerations of the existing root subtypes. The root sets
and their membership conditions remain the published ones. These definitions
choose enumerations and assert no canonical ordering.

This route is derived from the actual Lie decomposition and elementary module
finiteness. It does not assume `HasRelativeRootSystem`, prove root independence
or negation stability, or compare standard parabolic subgroup functors.
