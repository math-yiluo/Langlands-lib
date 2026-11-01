# Flattened intersection conjugation

For an arbitrary field `F`, two block shapes `B,C` of any rank, a permutation
`w`, refinements `S,R`, and supplied equalities
`sourceLevi F B C w = refinedLevi F B S` and
`sourceLevi F C B w⁻¹ = refinedLevi F C R`,
`flattenedIntersectionConjugation` is a group equivalence from
`(B.flatten S).Levi F` to `(C.flatten R).Levi F`. It composes the published
source flattened coordinate equivalence, equality relabeling, actual
intersection conjugation, target equality relabeling and the inverse target
flattened coordinate equivalence.

`flattenedIntersectionConjugation_embedding` proves that this map has exactly
the ambient formula `m ↦ permutation(w) * m * permutation(w)⁻¹`.
Surjectivity and this formula prove
`conjugatesLevi_flattened_intersections`: the representative conjugates the
entire flattened source Levi onto the entire flattened target Levi.
`flattenedIntersectionConjugation_eq_leviConjugation` identifies the map with
the existing whole-Levi conjugation for any proof of that concrete conjugacy,
using injectivity of the target embedding.

When `F` has a topology making it a topological ring,
`refinedIntersectionTransportFunctor` is the actual smooth middle transport:
source equality relabeling, inverse intersection conjugation and target equality
relabeling. `flattenedIntersectionTransportEquiv` compares its target flattened
pullback with whole-Levi inverse conjugation of the source flattened pullback,
for every actual smooth representation of the refined source subgroup.
The field and representation carrier universes are independent.

The representation comparison first proves the equality of the two acting
group elements by their ambient embeddings and the inverse-conjugation formulas.
Equality relabeling is compared with pullback by equality induction; its
representation carrier need not be definitionally the original carrier.
The two resulting equivalences are pulled back along inverse intersection
conjugation and flattened target coordinates, then composed with the identity
linear equivalence implementing the proved equality of group elements.

No minimal representative, positivity, cuspidality, finite length,
admissibility or whole-target hypothesis is used. Refinement witnesses are
supplied, and their existence is not asserted here. The module introduces no
character or normalization. This is an internal consequence of the existing
flattened coordinates, intersection conjugation, equality relabeling and smooth
pullback constructions, with no new literature assertion. It does not prove a
geometric sum, an Aubert identity or an analytic classification.
