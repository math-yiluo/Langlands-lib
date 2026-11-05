# The central additive-subgroup criterion in characteristic zero

Worker 1431. This internal deduction proves the central additive-subgroup
criterion over every characteristic-zero field at arbitrary universe `u`.
The group is an actual smooth connected affine group scheme satisfying the
existing `IsUnipotent` predicate. No structural theorem is an extra premise.

Start with a nonconstant morphism from the actual affine line. The published
pointed commutator-family construction produces a nontrivial smooth connected
affine central closed subgroup. Its image is nontrivial on the full functor of
points. Centrality and the monomorphism give commutativity of this subgroup.
The published closed-subgroup theorem supplies its unipotence for the original
representation-based predicate.

Every characteristic-zero field is perfect. The published
`perfectFieldUnipotentSplit` therefore supplies a finite represented split
series for the subgroup over the original field. The published
`HasSplitSeries.isVectorGroupOfDimension_of_commutative` converts this series
into natural vector coordinates on every relative scheme test. Nontriviality
of the image makes the coordinate dimension positive. A closed coordinate
line, composed with the central inclusion, is the required actual central
closed one-dimensional vector subgroup.

`centralAdditiveLineOfCharZero` chooses such a subgroup together with its
actual inclusion and the three stated properties. `criterion_of_charZero`
combines its existence with the existing unconditional forward implication.
The proof does not extend the base field or assume rational-point density.
The rational-point proposition appearing in a separate theorem of the imported
vector-line helper is not a premise of any declaration here.

This proves the characteristic-zero branch of the enclosing all-field target.
The positive-characteristic branch remains a separate obligation; the published
all-field proposition and its imports are unchanged.
