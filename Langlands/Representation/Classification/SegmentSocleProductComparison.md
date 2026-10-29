# Products of segment socles with a given segment list

Module `Langlands.Representation.Classification.SegmentSocleProductComparison`,
namespace `Langlands.PadicField.TopologicalData.SegmentProductDatum`.

This is a helper module for the proof of Zelevinsky, *Induced representations of
reductive p-adic groups II* (1980), Proposition 4.6. The source writes
`⟨Δ_1⟩ × ⋯ × ⟨Δ_r⟩` for a product of segment socles. That notation treats the
product as determined, up to isomorphism, by the segments `Δ_1, …, Δ_r`. In the
Library a product of segment socles is a `SegmentProductDatum` `d` with
`d.HasSegmentSocles`, and its blocks are only determined up to isomorphism. This
module supplies the comparison and the construction of such data from a list of
segments. These are our own (derived) bookkeeping lemmas. They are not quoted
from the source.

## Data from a list of segments

- `ofSegmentList l hn`: for a list `l` of segments whose degrees add up to `n`
  (`hn : (l.map Segment.degree).sum = n`), the datum of degree `n` with
  `length = l.length`, `segments = l.get`, and blocks the canonical segment
  socles `T.segmentSocle (l.get i)` (the socle of the induced representation of
  the segment, for the chosen representative of its beginning).
- `ofFn_segments_ofSegmentList`: the segment list of `ofSegmentList l hn` is `l`.
- `hasSegmentSocles_ofSegmentList hex l hn`: assuming
  `Classification.SegmentZelevinskyConstituentExistence F T` (Ze80 §3.1: every
  segment has a segment socle), `ofSegmentList l hn` has segment socles. This
  uses `IsSegmentSocle.isSegmentSocle_segmentSocle`: when some segment socle
  exists, the canonical one is a segment socle.
- `exists_of_list hex l hn`: under the same assumption, some datum with segment
  socles has segment list `l`.

## Sums and pairs

- `sum_map_degree_ofFn d`: the degrees of the segments of `d`, summed as a list,
  give `n`.
- `sum_rank_eq d`: `∑ i, (d.segments i).rank` equals the list sum of the ranks
  of `List.ofFn d.segments`.
- `ofFn_segments_eq_pair d h₂ Δ Γ`: for a datum of length two,
  `List.ofFn d.segments = [Δ, Γ]` holds exactly when `d.segments 0 = Δ` and
  `d.segments 1 = Γ`.

## Comparison

`nonempty_iso_of_ofFn_segments_eq h h₁ h₂`: if two data `d₁` and `d₂` of degree
`n` have the same segment list (`List.ofFn d₁.segments = List.ofFn d₂.segments`)
and both have segment socles, then `d₁.induced ≅ d₂.induced`.

Proof. The two segment lists have the same length, so the two data have the same
number of segments, and `List.ofFn` is injective, so the two families of
segments coincide. For each `i` the two blocks are segment socles of the same
segment. Both are therefore isomorphic to `T.segmentSocle (d.segments i)`
(`IsSegmentSocle.nonempty_iso_segmentSocle`). The normalized product induction
functor of the common block shape carries the resulting isomorphism of block
families (`Pi.isoMk`) to an isomorphism of the induced representations.
