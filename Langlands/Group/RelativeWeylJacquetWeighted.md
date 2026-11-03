# Weighted longest-representative cancellation

This internal helper assembles the published intrinsic Jacquet coefficient
and longest-survivor proofs into an identity with values in any additive
commutative group. It is intended for the finite sum step of the actual
rational-point Jacquet compatibility proof. It does not assert a geometric
lemma, transitivity of normalized functors, or an equality of actual
representation-theoretic terms.

The namespace is `Langlands.Group.RelativeWeylIndexing`. The construction
`jacquetWeightedExpansion cs J F` has value

```text
∑ I : Finset B, (-1)^|I| •
  ∑ w ∈ minimalReps cs J I, F w (simpleImage cs w I ∩ J).
```

`jacquetWeightedExpansion_eq_longest` proves that its value is

```text
∑ K ∈ J.powerset, (-1)^|K| • F (longestRep cs J) K.
```

The parameters are `B : Type u`, `W : Type v`, `[Group W]`,
`M : CoxeterMatrix B`, `cs : CoxeterSystem M W`, `[Fintype B]`,
`[Fintype W]`, `A : Type uA`, `[AddCommGroup A]`,
`J : Finset B` and `F : W → Finset B → A`. The ambient label,
group and additive-target universes are independent. The scalar action
is integer multiplication, and the signs are `(-1)^|I|` and `(-1)^|K|`.
Empty and full subsets, including an empty label type, are included.

`isMinimal_iff_right_subset_positiveSimpleSet` first separates minimality
into membership in `D(J,∅)` and containment of I in `positiveSimpleSet`.
It uses `minimalityLengthCriterion_proof`, without finiteness of W.
`jacquet_weighted_powerset_sum` groups each powerset sum according to
`simpleImage cs w I ∩ J`, applies `jacquetCancellation_proof` to its
integer coefficient, and applies `longestSurvivor_proof` to identify
the only surviving w. The theorem `jacquet_weighted_sum` exchanges the I
and w sums, restricts to the powerset using the first lemma, and applies
this weighted powerset calculation. The construction's reduction theorem
is exactly this last identity.

The only direct project import is
`Langlands.Group.RelativeWeylJacquetProof`, whose import closure supplies
the minimality and longest-survivor proofs and the indexing definitions.
The proof bodies use the exact declarations named above, `longestRep_mem`,
`mem_minimalReps`, `mem_positiveSimpleSet`, and the elementary finite-sum
and integer-action laws. There is no use of Langlands classification,
character independence, the geometric lemma, adjointness, cuspidal support
or normalized representation functors. Its imported Coxeter proofs have
their own published dependency explanations.

Provenance: this is an internal additive consequence of the published
`Langlands.Group.RelativeWeylIndexing.jacquetCancellation_proof` and
`longestSurvivor_proof`, corresponding to the finite cancellation in Aubert
1995, equation (1.9), printed pp.2182–2183 / PDF pp.4–5, registered as
`aubert-1995-duality`, SHA256
`57af9c46769f6edd8e142ddaf465e89acfa2f2147db222d26879a28a06df9693`.
Those pages and the retained source audit were read directly. This
additive packaging is internal derived content, rather than a separately
stated source definition. Actual-root sign, subgroup and functor comparisons
remain separate obligations. No use is made of Proposition 3.2 or the
original proof of Theorem 3.6.
