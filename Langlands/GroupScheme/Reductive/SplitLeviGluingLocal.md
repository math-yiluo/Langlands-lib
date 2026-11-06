# Actual local Levi comparisons and their root subgroups

Author: Worker 1444.

This internal derived construction supplies local objects for the graph route to
the common-torus isomorphism theorem. It combines published affine dynamic
centralizers, generic kernel cocharacters, intrinsic root subgroup realization
and transport. It does not prove the global gluing assertion.

Over an arbitrary field, `IsRankOneDirection i₁ ν` is the exact condition in
`SplitCommonTorusLeviGluingStatement`: any two actual roots of the first group
annihilating `ν` are integrally linearly dependent. `RankOneLeviHypothesis`
packages the same local premise, including every closed all-test representative
and every compatible torus factorization. No reductivity, root datum,
characteristic or perfection assumption is built into either predicate.

`LocalComparison` records actual representatives of the two dynamic
centralizers, their closed inclusions, torus factors, and an isomorphism
restricting to the given torus identification. `localComparison` constructs
these objects from affineness of the two ambient groups and the local premise.
It uses the canonical `Dynamic.Affine` centralizers and the existing
`Dynamic.torusFactor`, then applies that premise to obtain the comparison.
It does not assume a representative or a comparison map as another input.
The published smoothness and connectedness results show that these local
groups are smooth and affine when the ambient groups are smooth and affine,
and connected when their respective ambient groups are also connected.
Closedness of each torus factor follows from closedness of its ambient map.

For a split torus, a locally finite type affine first ambient group and any
nonzero character, the published generic kernel cocharacter annihilates that
character and no ambient roots independent from it. Finite type is used only
through finiteness of the actual roots. `kernelCocharacter_isRankOneDirection`
verifies the exact pairwise
condition by transitivity of dependence through this fixed nonzero character.
`rootLocalComparison` therefore constructs the local comparison for this
direction from the local premise. Neither result requires reduced roots.

`root_map_centralizer` proves that the full intrinsic root functor in a
cocharacter centralizer maps onto the ambient intrinsic root functor if its
character annihilates that cocharacter. The nonzero character of the split
torus is fpqc by the existing `characterFpqc` theorem. The published closed
embedding comparison identifies the preimage root functor; the published
zero-pairing containment places the whole ambient root functor in the
centralizer. The image of a preimage is the intersection with the inclusion's
range, so this intersection equals the entire ambient root functor.
Every equality is on all scheme tests, including nonreduced tests.

`RootComparison` retains actual smooth connected closed representatives of a
character's two local root functors and an isomorphism between them induced by
the local Levi comparison. `rootComparison` constructs this record using the
published realization theorem for nonzero characters and root transport under
an ambient isomorphism with the identity torus map. Classical choice selects the
representatives from their proved existence assertions. For a zero-pairing
character, `left_ambientRep` and `right_ambientRep` show that the composite
inclusions represent the ambient root functors themselves. This supplies
actual local root groups and maps, without assuming vector-line structure,
root reducedness or commutator formulas.

The provenance is internal composition of the cited imported Library results;
the predicates and records package the inputs and actual constructed maps.
They are intended for the graph construction motivated by Milne's
*Algebraic Groups* (2017), 23.16–23.18. The present unit does not assert that
an arbitrary collection of local comparisons glues, or identify a collection
indexed by all roots with a compatible global graph. Choosing simple roots,
constructing the global factors, establishing density and proving projection
invertibility remain obligations of the main gluing proof.
