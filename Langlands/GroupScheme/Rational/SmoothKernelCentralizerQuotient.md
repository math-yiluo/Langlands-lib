# Smooth quotients of full character-kernel identity centralizers

This internal supporting construction restricts a homomorphism to supplied
representatives of the full scheme-theoretic character-kernel centralizers.
The character and the acting commutative group scheme are unchanged; the target
action is conjugation by the composite of the source torus map and the
homomorphism. The restriction commutes exactly with the ambient inclusions.
This first construction works over every base scheme and requires no smoothness.

Over a field, supplied smooth affine representatives have actual identity
components. The restricted homomorphism factors through the target identity
component because its source is connected. The resulting
`kernelCentralizerIdentityMap` commutes with both ambient inclusions and, when the
acting group scheme is a split torus, with the induced torus maps.

For smooth affine ambient groups and a smooth ambient homomorphism, this
identity-component map is smooth and surjective on schemes. The proof uses the
published exact Lie image of each identity component: the sum of all weight
spaces indexed by integer multiples of the original character, including zero.
Smooth equivariance maps this entire span onto the target span. A target
tangent vector can therefore be lifted through the source inclusion and the
ambient differential. Injectivity of the target inclusion's differential and
the commuting square identify its image with the given vector. The published
surjective-differential criterion then proves smoothness and scheme
surjectivity. Over an algebraically closed field, rational points lift by the
published rational-lifting theorem.

There is no nonzero-character assumption, characteristic restriction, maximal
torus hypothesis, ambient connectedness assumption, or ambient surjectivity
assumption. The construction uses the full character kernel, without replacing
it by its reduced subgroup. It does not assert that an arbitrary lift of a
normalizer point normalizes the torus, and does not supply the facet-root
survival criterion or the final unramified facet root datum.

The provenance is internal composition of the all-test commutation property,
the identity-component factorization, `RootKernelIdentityWeights`,
`SmoothTangentWeights`, and `SurjectiveDifferentialProof`; no new
original-literature assertion is made.
