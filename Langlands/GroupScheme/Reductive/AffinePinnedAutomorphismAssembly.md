# Assembling the affine pinned automorphism-group conclusion

Authors: Worker 588; Worker 237 supplied the imported action homomorphism
and its centre-quotient properties.

This internal construction isolates the remaining geometric obligations and
assembles the exact conclusion of
`AffinePinnedAutomorphismGroupStatement` conditionally on them and on
`AffinePinnedIsomorphismTheoremStatement`.

For a supplied `AffinePinnedModel M` and an action `c` of `Gad` on its group,
`AutomorphismSplittingGeometry` consists of two explicit hypotheses:

- Every automorphism has a left factorization `σ = n * τ`, where `n` belongs
  to the image of the actual base-section homomorphism `c.basePointHom`
  and `τ` satisfies the exact pinned predicate with a based label.
- A pinned automorphism in that image has identity label.

`automorphismSplittingData` adds the identity, multiplication, basedness and
unique-existence properties of pinned representatives to these supplied
inputs. Unique existence uses the separate inverse-label conversion of the
supplied pinned full-faithfulness statement.

Given an actual fppf quotient by the full centre and its compatible descended
conjugation action, the image of `c.basePointHom` is normal.
`automorphismProjection` therefore applies the abstract quotient construction
to produce a homomorphism from actual group-scheme automorphisms to full
root-datum automorphisms. Its kernel is exactly that image, its range is
exactly `M.basedAutomorphisms`, and it sends each exact pinned representative
to its label. The three accompanying lemmas record these properties.

`affinePinnedAutomorphismGroup_of_splitting` proves the unchanged published
target from two explicit assumptions: pinned full faithfulness, and
`AutomorphismSplittingGeometry` for every connected affine pinned model and
every supplied centre quotient and compatible action. It packages the data
from the target as an `AffinePinnedModel`; the root index type is finite by
the target's fibrewise-root-datum hypothesis. The inner homomorphism is
`c.basePointHom`; its quotient-action faithfulness proves injectivity.
The projection properties and unique pinned representatives then give each
clause of the target.

All constructions are elementary compositions of the imported interfaces.
This unit proves neither the geometric hypotheses nor pinned full
faithfulness, and hence is a conditional reduction of the target.
