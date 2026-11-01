# Aubert exchange for actual length-one segments

Author: Worker 165.

The Prop-valued `Langlands.Aubert.LengthOneSegmentSocleHeadStatement` is the
existing actual segment exchange restricted to `Δ.length = 1`. It retains
arbitrary primes, the supplied p-adic field and topology, independent field
and carrier universes, and saturated carriers `Type (max uF uV)`. The theorem
`Langlands.Aubert.lengthOneSegmentSocleHead` proves this proposition.

For actual representations `πZ` and `πS` satisfying the existing strong
relations `T.IsSegmentSocle Δ πZ` and `T.IsSegmentHead Δ πS`, the conclusion is

```text
alternatingOperator F T Δ.degree [πZ]
  = (-1 : ℤ)^(Δ.degree - Δ.length) • [πS].
```

The classes are the canonical actual exact finite-length classes; their
finite-length witnesses follow from the irreducibility clauses of the supplied
relations. The quotient retains all short exact sequence relations, including
nonsplit ones. The operator and its support-dependent sign are unchanged.
This module proves no constituent existence and no exchange for segments of
length greater than one.

The proof first constructs `T.segmentInducedOneEquiv`. The published
`T.singleBlockNormalizedProductEquiv` evaluates the actual normalized
one-block induction at the identity and identifies it with its single tensor
factor. For a length-one segment that factor is the zeroth determinant twist.
The actual trivial-twist identity removes this twist. The equivalence displays
the necessary equality-of-rank reindexing from rank `r` to rank `1 * r`.
Equality elimination and the identity reindexing law show that this rank
transport preserves irreducibility and supercuspidality. Equivalence invariance
then proves `T.segmentInducedOne_supercuspidal`.

For `T.segmentConstituents_length_one`, choose the supercuspidal representative
from the supplied strong socle relation. The representative-independence
theorem `T.isSegmentHead_iff` expresses the supplied strong head relation for
the same induction. The actual socle embedding is nonzero because it is
injective and its source is irreducible. The actual head quotient is nonzero
because it is surjective and its target is irreducible. Irreducibility of the
length-one induction makes the embedding surjective and the quotient
injective. Their associated equivariant linear equivalences compose to an
equivalence between `πZ` and `πS`, and the first equivalence transfers
supercuspidality to `πZ`. Image and kernel uniqueness remain present in the
hypotheses; this boundary argument needs only the supplied maps.

Finally, `alternatingOperator_supercuspidal` from
`Aubert.SegmentSocleHeadBoundary` sends `[πZ]` to
`(-1)^(Δ.degree - 1) • [πZ]`. Equivariant equivalence gives equal canonical
classes for `πZ` and `πS`. The hypothesis `Δ.length = 1` identifies this exponent
with `Δ.degree - Δ.length`.

This is a derived result from actual single-block induction, trivial twists,
rank transport, representative invariance, elementary irreducibility and exact
class invariance, and the proved supercuspidal Aubert boundary. The generic
`Filtration.CentralEigenspaceSplitting` module supplies only the fact that an
irreducible representation has a nonzero vector. No segment classification,
multisegment exhaustion, signed effectivity, irreducible-image theorem, or
segment Jacquet formula is used. The general
`Langlands.Aubert.SegmentSocleHeadStatement` remains a separate proof
obligation.
