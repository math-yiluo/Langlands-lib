# Signed sums of intrinsic Coxeter intersections

This internal construction packages the finite additive assembly after
Aubert 1995, equation (1.8), printed p.2182, for an arbitrary finite Coxeter
system. Its input `f` takes values in any abelian group. In particular those
values may be integer-linear maps between actual exact finite-length
Grothendieck groups. No representation-theoretic identity is an input or a
conclusion of this module.

`signedIntersectionSum cs J f` is the signed sum over all ambient subsets
`I` and over `minimalReps cs I J`, evaluated at the constructed intrinsic
`intersectionSubset cs I J w`.

`sum_minimalReps_intersectionSubset` partitions the finite representative
set by that subset. On minimal representatives,
`standardIntersection_proof` identifies the corresponding intrinsic
intersection subgroup. `standardSubgroup_injective` then identifies its
equality test with equality of the subsets. Thus the fiber cardinalities
are exactly `intersectionMultiplicity cs J I K`.

`signedIntersectionSum_eq` exchanges the two finite sums and applies the
published `solomonCancellation_proof` to every `K` contained in `J`.
`sum_powerset_eq_sum_subtype` separately proves the bijection between
ambient subsets of `J` and finite subsets of the subtype `J`, by mapping
the latter along `Function.Embedding.subtype`. This embedding preserves
cardinality. `signedIntersectionSum_eq_sum_subtype` composes both results,
with exactly the indexing and unadjusted signs of the Levi alternating
operator. Empty root types and empty or full `J` require no exception.

The three universes for root labels, the Coxeter group, and the abelian
group are independent. The proof uses finite sums and integer scalar
multiplication; it uses neither classification nor characters, adjointness,
cuspidal support, or the geometric lemma.

The intrinsic declarations imported from `RelativeWeylSolomonProof` are
actual proofs, but they provide no actual-root realization, rational-point
Levi intersection identification, induction transitivity, Weyl conjugacy
of induced representations, or geometric-lemma expansion. Applying this
assembly to the rational induction compatibility target still requires
those representation and structural comparisons at their exact scope.
No conditional application in this module proves that target.

Provenance: this is an internal additive extension of the published finite
Coxeter cancellation proof, motivated by the rearrangement in the
registered original `aubert-1995-duality`, printed pp.2181–2182. It does not
use Aubert Proposition 3.2 or its defective application.
