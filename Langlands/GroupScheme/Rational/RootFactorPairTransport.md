# Actual opposite factor pairs in full-kernel identity components

This internal transport module compares the existing actual opposite-factor-pair
predicate before and after inclusion of the identity component of a smooth
closed representative of the full character-kernel centralizer. Its provenance
is the intrinsic-root comparison in
[`RootKernelIdentityRoot`](RootKernelIdentityRoot.md),
the torus factorization in
[`RootKernelIdentityTorus`](RootKernelIdentityTorus.md), invariance
of the full kernel centralizer under character negation in
[`RootFactorPairReflection`](RootFactorPairReflection.md), and the fpqc
character theorem in [`CharacterFpqcProof`](CharacterFpqcProof.md).
It is a derived construction and introduces no external geometric assertion.

A monomorphic group homomorphism reflects normalization through the same
torus automorphism: compose the normalization equality with the inclusion,
commute the inclusion with the actual inner automorphism, and cancel the
inclusion. Any group homomorphism carrying the same torus also carries
opposite factor pairs forward, by functoriality of root orbit extensions and
of normalization.

For the full-kernel identity component, character negation gives the same
centralizer representative and the same torus morphism into that component.
The latter equality follows by cancelling the component inclusion to the
ambient group. Apply the published intrinsic-root comparison at the negative
character and the proved fpqc property of every nonzero split-torus character.
This identifies the image of the opposite root subgroup with the original
ambient opposite root subgroup on every test scheme.

Consequently `kernelCentralizerIdentity_lift_oppositeFactorPair` lifts every
ambient opposite factor pair through this inclusion, preserving the two
ordered factors. The product of the lifted factors normalizes the lifted torus
exactly when its image normalizes the original torus.
`kernelCentralizerIdentityOppositeFactorPairsEquiv` constructs the actual
equivalence of the complete pair subtypes. Its forward map applies the
inclusion to each factor. This map is injective because the inclusion is
monomorphic, and it is surjective by the lifting theorem. No middle-root
membership or nonidentity hypothesis is needed for this equivalence.

The pointwise existence equivalence follows by taking nonemptiness of the
two pair types. The final theorem,
`forall_exists_oppositeFactorPair_kernelCentralizerIdentity_iff`, compares
existence for every nonidentity root point. For this step the published
intrinsic-root comparison at the original character lifts each ambient
root point too. Injectivity of the inclusion preserves and reflects
nonidentity, and the pointwise pair equivalence finishes both implications.

The component results retain arbitrary universe, field and characteristic
scope. They assume a split torus, a nonzero character, and a smooth affine
closed representative of the full scheme-theoretic kernel centralizer.
They require no reductivity, maximality of the torus, primitivity of the
character, or smoothness of its kernel. They retain the actual ordered pair,
torus, normalizer and rational-point map. They do not prove existence of a
factor pair, component reductivity, or a two-cell decomposition, and do not
prove `RootRankOneFactorizationStatement`.
