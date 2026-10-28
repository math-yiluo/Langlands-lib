# Actual adjacent segment-product refinements

Author: Worker 494.

This internal construction specializes `SegmentProductRefinement` to the
geometric adjacent merge and its swapped refinement from `AdjacentMergeShape`.
Both inner data retain every supplied segment occurrence and its actual
representation.

The original merged slot has the complete block list `[d.blockAt j,
d.blockAt (j + 1)]`. The swapped merged slot has the reversed complete list.
Away from that slot the two inner data are equal, including their actual
bundled smooth factors. The outside equality follows because the adjacent
transposition fixes the unique inner label in every outside component.

The original merged datum has length two and its segment list is exactly the
original adjacent segment list. Every inner original datum inherits
`HasSegmentSocles` from the full datum by restriction to its actual labels.
`adjacentSwappedDatum_merged_eq` identifies the swapped merged datum with
the original merged datum permuted by its own adjacent swap at zero.
Its proof uses equality of complete block lists and the elementary fact that
the transposition of a two-element finite index reverses `List.ofFn`.

`adjacentInducedEquiv` and `adjacentSwappedInducedEquiv` apply the closed ordered
regrouping theorem with the exact geometric coordinate identities. Their targets
use the same outer shape and the actual original or swapped inner products.
`adjacentSwapInducedEquiv` lifts a supplied actual equivalence at the merged
slot by the outside datum equalities, applies the normalized induction
equivalence on the common outer shape, and composes the two regrouping maps.

The merged-slot equivalence remains an input. This file establishes no
two-segment commutation, constituent existence, linked reduction, or
multisegment exhaustion. It has arbitrary supplied topology and prime,
independent field and segment carrier universes, and no restriction on the
total rank beyond the existence of the displayed adjacent positions.
Its provenance consists of the cited Library constructions and elementary
finite label identities; it makes no additional claim from external literature.
Its project imports use the closed ordered regrouping proof and basic segment
data, replacement, permutation and induction equivalences. They use no analytic
segment classification, special-head exhaustion, quotient coverage, tempered
uniqueness, square-integrable classification or exhaustion, or regular
exhaustion conclusion.
