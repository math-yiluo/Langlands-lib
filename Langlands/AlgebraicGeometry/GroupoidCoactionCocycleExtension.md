# Extensions associated to groupoid cocycles

Author: Worker 148.

This internal algebraic unit constructs an extension of the regular coaction
by a given coaction θ on M, associated to an additive one-cocycle
x ∈ C ⊗[B] M. The rings B and C and the module M lie in the same arbitrary
universe u, as in the final geometric target. The relation satisfies
`RingEtaleEquivalenceRelation t`.

`regular` is the canonical coaction on B, sending b to t(b) ⊗ 1.
`cocycleExtensionMap` is the additive map on M × B sending (m,b) to

    (C ⊗ inl)(θ(m)) + t(b) · ((C ⊗ inl)(x) + 1 ⊗ (0,1)).

For a cocycle x, `cocycleExtension` proves that this map is a coaction.
Its semilinearity follows from that of θ. The counit at the universal
identity follows from the counit of θ and the vanishing of x there, proved
in `GroupoidCoactionCocycleUniversal`. For composition, it suffices to
check the inclusion of M and the extra generator (0,1). On the inclusion,
the equation is the coassociativity of θ; on the generator, it is the
cocycle equation for x. Additivity and semilinearity extend it to every
(m,b). The implementation verifies these identities for the raw map and
then uses the published `GroupoidCoaction.ofUniversal` constructor.

`cocycleExtension_inl_isHom` and `cocycleExtension_snd_isHom` prove
equivariance of the standard inclusion and projection. Their underlying
linear maps give the split exact sequence of B-modules

    0 → M → M × B → B → 0.

`oneCohomologyVanishes_of_isAcyclic` applies the published invariant-lifting
predicate to this extension and the invariant element 1 of the regular
coaction. An invariant lift has the form (m,1). Its first tensor component
satisfies θ(m) + x = 1 ⊗ m, so x is the coboundary of −m.

`oneCohomologyVanishes_iff_isAcyclic` combines this implication with the
published sufficient criterion. The latter needs flatness of C over B,
which follows from the étaleness field of the relation.

These constructions and proofs are derived directly from the published
coaction and cocycle equations. The equivalence concerns the two internal
predicates; it does not compare them with a separately constructed
cohomology group. No geometric vanishing or affine descent is established.
