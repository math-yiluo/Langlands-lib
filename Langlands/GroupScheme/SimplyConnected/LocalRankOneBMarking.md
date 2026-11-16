# Actual rank-one type-B markings and the two small ranks

This internal contribution to Task 5783 proves a conditional marking
reduction for type B and unconditional identifications for ranks one and
two. The higher-rank reduction explicitly assumes
`LocalAnisotropicCartanComponentsStatement`; that premise and the full
local rank-one enumeration remain unproved.

All the results use actual `TitsIndexData` and a supplied equivalence
identifying every ordered Cartan entry with Mathlib's `CartanMatrix.B n`.
The star action is the full absolute Galois action. All field and residue
characteristics and the arbitrary universe parameter are retained.

## Rigidity and rank one

`TitsIndexData.starIsTrivial_of_type_B` uses the transferred type-B matrix
rigidity to fix every actual vertex under every full Galois element, for
`2 ≤ n`. This argument works over any field.

`TitsIndexData.hasRankOneInnerAIndex_one_of_type_B_one` also works over any
field. A one-vertex actual diagram has trivial star action. Split rank one
then makes its distinguished set the unique vertex. The published
small-rank normalization identifies this marked B1 matrix with the exact
predicate `HasRankOneInnerAIndex 1`.

## Conditional marking in higher rank

Over a nonarchimedean local field,
`localRankOneTypeB_marking_of_components` assumes the explicit local
anisotropic-component premise and `2 ≤ n`, and concludes that exactly one
vertex is distinguished. Its zero-based number `j` satisfies
`j.val + 2 = n` or `j.val + 1 = n`. The conclusion is the exact
`IsNumberingOf` predicate, together with triviality of the full star
action. Simple connectedness and absolute almost simplicity are not
needed for this conditional consequence.

The proof first combines rigidity with the published rank-one orbit
theorem to obtain a singleton distinguished set. If its vertex were
neither of the final two vertices, both ends of the double edge would
belong to the actual zero diagram. The explicit component premise makes
the Cartan entries of that zero diagram symmetric. The final type-B
edge has unequal ordered entries, giving a contradiction. Injectivity
of the supplied numbering then proves both directions of the exact
marked-set comparison.

## Rank two

`localRankOneTypeB_two_index` assumes a nonarchimedean local field,
simple connectedness, absolute almost simplicity and split rank one,
with a supplied B2 Cartan numbering. It proves that the distinguished
vertex is exactly zero-based vertex zero and that
`HasRankOneCIndex 2` holds. This theorem has no component premise.

Interchanging the two vertices identifies the entire B2 matrix with C2.
The published `localRankOneTypeC_presentation_and_marking` gives precisely
vertex one in this new C2 numbering. Transporting membership back across
the swap gives vertex zero in the supplied B2 numbering, and the
published small-rank normalization gives the exact C2 alternative,
including its full star action. The two finite swap comparisons use
ordinary kernel-checked `decide`.

These results compose actual-index orbit, kernel-symmetry, type-C marking
and small-rank normalization prerequisites with the elementary
type-B transpose argument. They introduce no new literature claim and
prove neither the exclusion of B ranks at least three nor the
unconditional `LocalRankOneTitsIndexStatement`.
