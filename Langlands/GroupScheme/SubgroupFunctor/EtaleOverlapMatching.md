# Pairwise overlap compatibility and all-test étale matching

This internal helper connects equality of subgroup functors on the actual
pairwise overlaps of an étale cover to the all-test matching hypothesis of
`SubgroupFunctor.etaleDescentSubgroup`. It does not construct local opposite
Borels or prove their overlap equality.

For maps `f : U → S` and `g : V → S`, `Descent.pairwiseOverlapIso` identifies
the two iterated pullbacks of an ambient group scheme `G` to `U ×_S V`.
It composes the existing comparisons from those two pullbacks to the same
direct pullback of `G`. The associated projection theorem states that this
identification preserves the projection to `G`.

For arbitrary subgroup functors `F` over `U` and `E` over `V`, the membership
transfer lemma assumes that the inverse image of the second subgroup along
this identification is contained in the first subgroup on the overlap.
Given scheme maps into the two local ambient groups with the same original
projection, it transfers membership in `E` to membership in `F`. The proof
constructs the induced map of the test scheme to the pairwise overlap, lifts
the first point to the iterated pullback, and uses the projection theorem
and pullback uniqueness to identify its transported second projection.
The absolute `schemeCondition` interface then converts the overlap
containment back to the desired local membership.

For a small jointly surjective étale cover, applying this transfer to an
arbitrary comparison of local test schemes proves
`isMatchingEtale_of_pairwiseOverlap_le`. The equality version
`isMatchingEtale_of_pairwiseOverlap_eq` uses equality in the required
direction. These statements concern subgroup functors on all test schemes;
no representability, closedness, reductivity, or restrictions on the base
scheme are assumed.

The range corollary `isMatchingEtale_range_of_pairwiseOverlap_eq` accepts
local group homomorphisms whose ranges become equal after pulling them to
the pairwise overlap and composing with their comparisons to the common
direct pullback of `G`. Inverse image along the first comparison converts
this equality to the preceding subgroup-functor interface. The existing
range transport and range base-change theorems justify that conversion.
The local homomorphisms need not be monomorphisms for this corollary.

The construction and proofs are categorical consequences of the existing
Library pullback comparisons and subgroup membership definitions. Their
provenance is internal support for the descent step of the opposite-Borel
argument, without an additional literature assertion.
