# Associated simple-label and finite-subset indexing

This internal construction supplies the finite-index transport needed after
the Jacquet cancellation in Aubert's Theorem 1.7(2), printed pp. 2182–2183 of
the registered source `aubert-1995-duality`. It does not assert a representation
identity or an identification of actual parabolic subgroups.

`simpleConjugationEquiv` constructs the generic simple-label equivalence
from the visible conditions that every source label maps to a target simple
reflection and that its constructed image covers the target. Its proof uses
`simple_reflection_injective` to prove injectivity and the image definition to
prove surjectivity. `simpleConjugationEquiv_conj` records the defining
conjugation equation. These conditions are proved, rather than assumed, when
the equivalence is specialized to the associated subset below.

For an arbitrary Coxeter system with finite simple-label and group types,
`associatedSimpleEquiv` sends the actual subtype of `associatedSubset cs J` to
the subtype of `J`. Its conjugation law is implemented using the inverse
simple-label map in the definition of `associatedSubset`, the published
`associatedSubsetLaws_proof`, and injectivity of the Coxeter simple reflections.
`associatedFinsetEquiv` applies this equivalence to finite subsets and preserves
their cardinalities. The construction retains the chosen `longestRep cs J`.
`simpleImage_associatedFinsetEquiv` identifies its ambient finite-subset image
with the literal `simpleImage` under that element. The two finite subsets are
read in the ambient simple-label type by `Finset.map` of the subtype embedding.

`sum_powerset_eq_sum_finset_subtype` converts a powerset sum to a sum over the
finite subsets of the literal subtype `J`. The proof supplies the subtype map
and its inverse to `Finset.sum_bij`. `signed_sum_associatedFinsetEquiv` then
uses `Fintype.sum_equiv`, the ambient image law, and preservation of cardinality
to rewrite the signed sum over `J.powerset` as the signed sum indexed by the
finite subsets of `associatedSubset cs J`. The coefficients remain
`(-1 : ℤ) ^ I.card`. This holds with values in every additive commutative group
in an independent universe, so it applies to exact-K0 linear maps.

`positiveSimpleSet_longestRep` identifies the longest representative's right
ascents with the associated subset. The forward inclusion uses
`mapsIntoSimple_longestRep`; the reverse inclusion uses its left minimality
and the published `minimalityLengthCriterion_proof`. This proof only uses
intrinsic Coxeter combinatorics. Both universes are independent, and empty
simple-label types and empty or full `J` are included.

The literature motivates the finite-index transport. The explicit equivalences
and their Lean implementation are derived infrastructure, rather than a
separately numbered assertion in the source.

The implemented declarations depend on `simple_reflection_injective`,
`associatedSubsetLaws_proof`, `mapsIntoSimple_longestRep`,
`minimalityLengthCriterion_proof`, and elementary finite-sum and group laws.
Their proofs do not use any representation-theoretic declaration, including
Langlands classification, character independence, the geometric lemma,
adjointness, or cuspidal support. The two imported project proof modules expose
the intrinsic Coxeter results needed above; they do not supply an identity of
normalized functors or an actual subgroup-family comparison.
