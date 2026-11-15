# Exact neighboring Speh target from a rectangle constituent bound

This internal module defines the proposition
`NeighborRectangleConstituentLengthBound` and proves
`spehNeighborProductIrreducibility_of_rectangle_bound`: the published
proposition `Langlands.Aubert.HeadProductLeadingTermStatement` together with
`NeighborRectangleConstituentLengthBound` implies the exact published
proposition `SpehNeighborProductIrreducibility`, with its independent
universes. Both inputs are explicit hypotheses here. No unconditional Speh
result is claimed by this module.

## The bound

`NeighborRectangleConstituentLengthBound F T` is a definition and asserts no
proof. It concerns an actual cuspidal datum `ρ`, natural numbers `k ≥ 2` and
`l > 0`, and actual Langlands heads `A` and `B` (weak data `dA`, `dB`) whose
multisegments are the centered rectangles `tadicMultisegment ρ (k+1) l` and
`tadicMultisegment ρ (k-1) l`. It says that every actual irreducible
subquotient `C` of the normalized product of `A` and `B`, with any weak head
datum `dC`, has all segments of length at most `l`. The cuspidal datum need
not be unitary. In Badulescu (2014), proof of Theorem 1(b)(ii), this is the
statement that every constituent of u(δ,k+1) × u(δ,k−1) has a Langlands
multisegment whose segments are no longer than those of the rectangles.

## Proof of the reduction

`length_eq_of_mem_tadicMultisegment` states that each member of a centered
rectangle has the prescribed length.

For each actual discrete-series datum in the target, the segment
classification adapter (`SpehMultisegmentAdapters`) chooses a segment `Δ`
describing the given discrete-series action. The adapter keeps this action
for both neighboring Speh lengths. It identifies the given actual
representations as weak heads and identifies their labels with the centered
rectangles at the common midpoint cuspidal datum. All segments in their sum
have length `Δ.length`. `isIrreducible_of_constituent_segment_length_le`
(`SpehNeighborProductAssembly`), applied to `hH` and the bound, gives actual
irreducibility. The published equality between the normalized binary functor
and its positive-rank version gives exactly the product in the unchanged
target statement.

## Provenance

This is a derived internal reduction from the imported interfaces. It does
not supply the head-product proof, MW correctness, the rectangle duality
calculation or the constituent bound.
