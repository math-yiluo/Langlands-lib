# Target transport of strong irreducible heads

The algebraic lemma preserves the common, arbitrary carrier universe and the
group universe. `IsIrreducibleHead.of_targetEquiv` transports a strong head through
an actual equivalence of its target. The irreducibility proof is transported by
the published equivalence-invariance lemma; composition with an injective
equivalence leaves the quotient map's kernel unchanged.

The existing theorem and its proof were moved unchanged from
[SegmentSocleDecreasingHead](SegmentSocleDecreasingHead.md) so that both
that module and [SegmentHeadContragredient](SegmentHeadContragredient.md)
reuse one declaration. This is an internal transport lemma for the existing
strong-head predicate; it assumes no constituent-existence or classification
result. Its only project dependencies are ConstituentRelations and the
existing representation-isomorphism invariance proof.
