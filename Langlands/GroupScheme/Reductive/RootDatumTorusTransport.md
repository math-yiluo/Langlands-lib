# Actual root data under a change of torus

Provenance: internal. This module transports the published actual-root-datum
predicate along supplied isomorphisms of the acting torus and ambient group.
It is an interface needed when the pinning torus is identified with the base
change of a descended torus, rather than literally equal to it.

`torusTransportRootDatum` applies `RootPairing.map` to the integral character
and cocharacter equivalences of the supplied torus isomorphism, leaving root
indices unchanged. Its roots, coroots and pairing have the displayed transport
formulas; its reflections intertwine the character equivalence. The reflection
formula follows by expanding the integral reflection and using preservation of
addition, scalar multiplication and the transported pairing.

`IsRootDatumOf.torusTransport` assumes the actual torus and ambient-group
isomorphisms and their inclusion square. It proves the full actual-root-datum
predicate for the transported datum. The pairing clause follows from
`latticePairing_congr`; the root-range clause follows from the published actual
root-set transport theorem. For each reflection, transport the supplied actual
normalizing point and torus automorphism using
`IsNormalizingPoint.transport`. Inverse precomposition on characters intertwines
this transported automorphism with the displayed transported reflection.

The two fields of lattices belong to the actual commutative group schemes,
and the normalizing points remain actual rational points. The result assumes
no finite root index set, splitness, reductivity, field extension or Galois
action. Both ambient groups are affine over an arbitrary field; the index
universe is independent. This module asserts no existence of a root datum or
pinning and does not prove the even-chain Galois-data existence target.
