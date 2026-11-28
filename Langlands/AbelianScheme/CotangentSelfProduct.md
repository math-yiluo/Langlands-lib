# Cotangent sections of an abelian self-product

For an abelian scheme `B` over a scheme `S`, `cotangentSelfProductEquiv B`
identifies the global sections of the identity cotangent module of
`DualMapEquality.square B` with two copies of the identity cotangent sections
of `B`. The equivalence is linear over the global functions on `S`. The
forward map restricts along the two coordinate axes. Its inverse adds pullbacks
along the two projections.

The two axis restrictions of a projection pullback are the identity and zero
by composition of cotangent maps and the vanishing for the trivial group
homomorphism. In the other direction, take the difference of the sum of the
two axis and projection composites and the identity of the product cotangent
module. Precomposing this difference with either projection pullback gives
zero. The product cotangent extensionality lemma
`GroupScheme.cotangentMap_fst_snd_ext` makes the difference zero. Taking global
sections preserves composition, addition, identities and zero maps. These
identities give the two inverse equations for the linear equivalence.
