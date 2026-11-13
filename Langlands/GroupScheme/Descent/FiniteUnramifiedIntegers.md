# Actual integer rings at finite unramified stages

This internal comparison identifies `FiniteUnramified.integerCoefficients F E`
with the actual spectral integer ring `LocalGalois.extensionIntegers F E` when
`E` is contained in the inertia fixed field. The two maps preserve the underlying
separable-closure element. The spectral norm tower equality verifies the integer
bound in both directions, and subtype extensionality proves the inverse laws.

`integerCoefficientsAut` transports the published spectral integer automorphism
along this ring equivalence. Its coercion lemma records its actual field value.
No descent datum or tensor product decomposition is asserted here.
