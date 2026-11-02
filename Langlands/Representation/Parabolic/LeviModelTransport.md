# Smooth and exact-K0 transport between actual GL Levi models

Author: Worker 585.

This internal adapter uses the existing full smooth complex representation
categories and exact finite-length Grothendieck groups. For an arbitrary natural
rank, block shape and commutative topological ring `F : Type uF`, the product
Levi, its embedded block-diagonal matrix subgroup and the actual quotient of
the upper parabolic by its radical are continuously multiplicatively equivalent.
The smooth representation carrier universe `uV` is independent of `uF`.
Rank zero and its empty product are included.

`productToEmbeddedLevi` pulls an action back along the inverse of the existing
product-to-embedded Levi equivalence. At an embedded matrix `m` its action is
the original action at the diagonal-block projection of `m` viewed in the
parabolic. `productToQuotientLevi` pulls back along
`parabolicQuotientLeviContinuous`. The class of a parabolic matrix `g` acts by
the original action at its diagonal-block projection.
`embeddedToQuotientLevi` uses the composite quotient-to-embedded equivalence.
The displayed action formulas use the literal original vector spaces.
All three functors retain the underlying linear map of every intertwiner;
the corresponding map formulas are definitional equalities.

`embeddedLeviK0Equiv`, `quotientLeviK0Equiv` and
`embeddedToQuotientLeviK0Equiv` apply the existing generic
`FiniteLengthGrothendieckGroup.pullbackEquiv` to those group equivalences.
Their inverses are pullback along the inverse group equivalences, as in that
generic construction. These are integer-linear equivalences on the full
quotients by actual short exact sequences, rather than maps on chosen
irreducible labels. Finite length is preserved by the generic surjective
change-of-group theorem, and short exactness is preserved because the linear
maps are unchanged. The three class formulas hold for any proofs of finite
length of the inputs and outputs. Such output proofs always exist by the
generic preservation theorem. `embeddedToQuotientLeviK0Equiv_comp` proves that
transport directly to the quotient agrees on all virtual classes with transport
through the embedded model.

The provenance is specialization of the already constructed smooth pullback
and exact-K0 functors to the actual matrix group maps. The new group topology
module uses no representation-theoretic theorem. The representation module
imports `Smooth.FiniteLengthGrothendieckTransport`, which itself imports
`Classification.FiniteLengthProof` and the compact-coefficient transport
module. Its finite-length input is
`FiniteLengthAssembly.finiteLength_comp_surjective_iff`, proved by the
order-isomorphism of subrepresentations under a surjective group map and
invariance of module length. No transitive classification-independence claim
is made for this import closure.

These model transports are prerequisites for the shared general-to-GL adapter.
They do not identify general normalized induction or Jacquet functors, construct
a general reductive datum, or assert equality of Aubert operators. Those
comparisons retain the positive half-modulus for induction and inverse
half-modulus for Jacquet restriction and remain separate host-task obligations.
