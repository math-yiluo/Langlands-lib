# Full-kernel centralization and coroots of actual factor pairs

This internal construction associates an actual integral coroot to a supplied
root-flipping opposite factor pair. It also proves that the pair represents
the exact predicate `IsRelativeReflection` on the existing rational relative
root span. Pair existence and the root-flip premise remain inputs.

The provenance is a composition of the published orbit-extension
kernel-centralization lemma in
[`QuotientActionComparisonProof`](QuotientActionComparisonProof.md), the
full-kernel integral-coroot extraction in
[`RootKernelReflection`](RootKernelReflection.md), and the rational evaluation
and spanning constructions in
[`RootReflectionAssembly`](RootReflectionAssembly.md). These are reused by
their Lean declarations. The module supplies the transport between opposite
characters and the application to the actual factor-pair predicate; it makes
no new external-source assertion.

`kernelCentralizer_le_neg` works over an arbitrary base scheme and for every
test scheme and refinement. A point in the full kernel of the negative
character also belongs to the full kernel of the original character: character
evaluation sends negation to inversion, and the inverse of its value is one.
The proof uses `kernelPointsEquiv` to lift that same torus point to the original
kernel. The assumed commutation therefore applies to it. Applying the inclusion
twice gives `kernelCentralizer_neg`. This treats the full scheme-theoretic
kernel, including nonsmooth kernels.

For a point of the actual root subgroup, its defining orbit extension gives
full-kernel centralization by
`mem_kernelCentralizer_of_isOrbitExtension`. This proves
`subgroup_le_kernelCentralizer`; the equality for opposite characters proves
`opposite_subgroup_le_kernelCentralizer`. Thus both directions centralize the
same kernel. Over an arbitrary field,
`IsOppositeFactorPair.mem_kernelCentralizer` multiplies these three subgroup
memberships for the two opposite factors and the middle root point. No
affineness or torus monomorphism is required for these containments.

For the coroot construction, the torus is split, its homomorphism to the group
is monomorphic on underlying schemes, the character `a` is nonzero, and the
middle rational point lies in the actual `a` subgroup. A supplied pair
`p` satisfies the existing `IsOppositeFactorPair i a x p`. Its normalizing
product is additionally assumed to send `a` to `-a` under `weylAction`.
`IsOppositeFactorPair.corootOfFlip` applies
`IsSplitTorus.existsUnique_coroot_of_mem_kernelCentralizer` to that product
and the proved full-kernel centralization, then chooses the resulting actual
cocharacter. Its specification states both that the pairing with `a` is two
and that the normalizer acts on every integral character `χ` by
`χ ↦ χ - ⟨χ, corootOfFlip⟩ • a`. The imported existence theorem also ensures
uniqueness of a cocharacter with these two properties.

For `IsOppositeFactorPair.isRelativeReflection_of_flip`, the ambient group is
affine and `a` belongs to the existing relative-root set, hence is nonzero.
The proof uses `RelativeRootSystem.corootFunctional` of the constructed
cocharacter as the rational linear form in `IsRelativeReflection`. Evaluation
on the root vector is two by `corootFunctional_rootVector` and the integral
self-pairing. The relative Weyl action equals the resulting reflection on each
actual root vector: the action is the rational extension of `weylAction`,
and the formula follows from the integral specification by preservation of
subtraction and integer scalar multiplication. Since these root vectors span
`relativeRootSpan i`, the two linear equivalences agree everywhere.

No connectedness, reductivity, maximality, characteristic, primitivity,
reduced-root-system or finiteness assumption is used. Nonidentity of the middle
point is also unnecessary for these conditional assertions. This module does
not construct a normalizing factor pair, prove that an arbitrary pair flips
the root, or prove the extra conclusions for a nonmultipliable root. The
unrestricted `RootRankOneFactorizationStatement` remains open.
