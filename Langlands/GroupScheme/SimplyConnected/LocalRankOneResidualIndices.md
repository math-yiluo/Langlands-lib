# Three residual patterns of actual rank-one indices

These internal predicates describe three concrete patterns on an actual
`TitsIndexData G` over any field. They impose no locality, simple connectedness
or split-rank premise. Their names record the rank-one marking patterns for
which they are used; they do not assert that these patterns occur.

* `HasRankOneHigherBIndex` requires an exact type-B Cartan numbering with
  `n ≥ 3`, exactly one distinguished vertex `j`, and trivial full star action.
  In zero-based notation, `j.val + 2 = n` or `j.val + 1 = n`.
* `HasRankOneG2Index` requires the exact Mathlib `G₂` Cartan matrix, exactly
  vertex zero distinguished, and trivial full star action. For the Library's
  root-on-coroot convention, this is the long-root vertex.
* `HasRankOneD4InnerOrNoFixedLeafIndex` requires the exact type-D4 matrix,
  exactly its central vertex (zero-based vertex one) distinguished, and either
  trivial full star action or absence of a globally fixed leaf. A globally
  fixed leaf is an actual vertex `a` numbered differently from one for which
  every element of the full absolute Galois group fixes `a`.
* `HasResidualRankOneIndex` is the disjunction of these three properties.

Every numbering uses the existing `IsNumberingOf`: it compares every ordered
integral Cartan entry and the distinguished subset in both directions.
`StarIsTrivial` and leaf fixation quantify the full group
`SeparableClosure K ≃ₐ[K] SeparableClosure K`. In the absence condition, the
vertex is quantified before the Galois element, so it excludes a single leaf
fixed by the entire image; it does not require any individual Galois element
to act without fixed leaves.

The provenance is internal: these properties collect the concrete conclusions
of `localRankOneTypeB_marking_of_components`, `G2_rankOne_marking` and
`localRankOneD4_central_marking`, together with the complementary case to the
fixed-leaf outer-D4 reduction. They are properties of a supplied actual index,
not aliases of a closed theorem or assertions of an exclusion. The accompanying
`LocalRankOneResidualReduction` gives a conditional reduction to these patterns.
No arithmetic exclusion, trialitarian exclusion or unconditional enumeration
is proved here. Every field characteristic and universe parameter is retained.
