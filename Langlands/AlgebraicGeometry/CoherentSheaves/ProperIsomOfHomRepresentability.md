# Isom representability from Hom representability

`properIsomRepresentability_of_properHomRepresentability` proves the
implication `ProperHomRepresentabilityStatement.{u} →
ProperIsomRepresentabilityStatement.{u}` between the two Library statements.
It is conditional and does not prove either statement.

## Proof

Fix a proper, locally finitely presented `f : X ⟶ S`, a scheme `T` over `S`,
and families `M N : FamilyGroupoid f T`. The conclusion of
`ProperHomRepresentabilityStatement` for a pair of families is by definition
`IsAffineFinitePresentationRepresentable (FamilyGroupoid.homPresheaf f M' N')`.
Apply it to the four pairs `(M, N)`, `(N, M)`, `(M, M)` and `(N, N)`. Then
`of_isLimit_binaryFan` with Mathlib's `FunctorToTypes.binaryProductLimit`
shows that the pointwise products `homPresheaf f M N × homPresheaf f N M` and
`homPresheaf f M M × homPresheaf f N N` are representable in the same sense.
The Isom presheaf is the point of the limit fork `isomPairFork f M N`
(`isomPairForkIsLimit`). The fork is of the composite and identity maps
between these two products. Therefore `of_isLimit_fork` shows that the Isom
presheaf is represented by a scheme affine and locally of finite presentation
over `T.left`, which is the conclusion of `ProperIsomRepresentabilityStatement`.

## Provenance

This is the argument of the proof of Stacks Project Proposition 99.4.3
(Section 99.4, Tag 08K7), which derives the Isom functor from the Hom functors
of Proposition 99.3.10. The retained original is `08K7.html` in registered
source `stacks-isom-functor-08k7-2026-11-02` (folder SHA-256
`a05b61ba562e7e65dd2b64446e779a6bb67af1846c0a00f4a656d64a2b2c27b5`). The
equalizer construction is in `IsomHomEqualizer`, and the closure of
representability under products and equalizers is in
`AlgebraicSpace.AffineFinitePresentationRepresentable`.
