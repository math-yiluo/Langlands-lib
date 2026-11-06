# Simple-preserving pairs for a coatom source

This internal unit proves
`Langlands.Group.RelativeWeylIndexing.CoatomSimpleSurvivorBoundStatement`
for any finite Coxeter system, with independent universes for its simple labels
and group. No connection between these labels and an algebraic group's roots
is assumed or established here.

For a finite subset `J` of simple labels, `simpleSurvivorPairs cs J` is the
finite set of pairs `(I,w)` satisfying all three conditions:

- `I.card = J.card`;
- `w` is a minimum in the actual double coset `W_I w W_J`;
- conjugation by `w` sends every simple reflection labelled by `J` to a
  simple reflection labelled by `I`.

The construction uses the actual Coxeter group elements and its finite subsets.
Different representatives or target subsets remain different indices.

`fullIntersectionPairs cs J` uses the same cardinality and minimality
conditions, with `intersectionSubset cs I J w = J` as its third condition.
At a minimal representative, the proved
`exists_conj_simple_eq_of_isMinimal` makes every source simple reflection
whose conjugate lies in `W_I` conjugate to a simple reflection labelled by
`I`. Conversely a simple image labelled by `I` lies in `W_I`.
`intersectionSubset_eq_source_iff_mapsIntoSimple` proves the equivalence,
and `fullIntersectionPairs_eq_simpleSurvivorPairs` identifies the two
finite sets without changing indices.

For `J = univ.erase b`, `coatom_simpleSurvivor_classification` proves that each
such pair is either `(J,1)` or
`(associatedSubset cs J, (longestRep cs J)⁻¹)`.
If `w = 1`, injectivity of the simple-reflection map gives `J ⊆ I`; the equal
cardinalities give equality. Otherwise `w` has a right descent. Double-coset
minimality makes every label in `J` a right ascent, so that descent must be at
`b`. Hence the right ascent set is exactly `J`. The proved longest-survivor
criterion, applied with target `I`, then gives `w = longestRep cs I`.
The proved formula for its right ascents gives `J = associatedSubset cs I`.
The associated-subset involution and inverse-longest formula identify `I` and
`w` as claimed.

`canonical_simpleSurvivorPairs` verifies both displayed pairs for every `J`.
For the second, left minimality is that of the longest representative for
`associatedSubset cs J`; its right ascent set is `J`, which supplies right
minimality. The proved longest-representative simple-image law supplies the
conjugation condition. `simpleSurvivorPairs_coatom` therefore gives equality
with the displayed two-element finset. `coatomSimpleSurvivorBound` takes its
cardinality to obtain the bound two. Empty label types are included: the final
universal assertion over `b` is then vacuous.
`card_fullIntersectionPairs_coatom_le_two` transfers the same bound to
full source intersections.

The provenance is an internal deduction from
`minimalityLengthCriterion_proof`, `simple_reflection_injective`,
`longestSurvivor_proof`, `positiveSimpleSet_longestRep`,
`associatedSubset_involutive`, `longestRep_associatedSubset`,
`associatedSubsetLaws_proof`, `exists_conj_simple_eq_of_isMinimal`, and
elementary finite-set facts. The proof uses
no representation-theoretic result, classification, support theorem or
geometric lemma.

This unit supplies only an intrinsic combinatorial count. Applying it to actual
Jacquet modules still requires a root/Weyl realization, an indexing comparison
for surviving geometric pieces, a finite family of actual target Levis, and
detection of every irreducible subquotient. It does not prove a maximal-Levi
induction length bound or a unitarizable-constituent theorem.
