# Exponent-sorted orderings of segment-head products

Author: Worker 4988. Module `Langlands.Representation.Classification.A6iiSorting`,
namespace `Langlands.Classification.A6ii`. Internal helper for the proof of Tadić's
Corollary A.6(ii) (`IrreducibleLanglandsHeadProductProof`). It repeats, for a supplied
segment datum, the sorting step of the published `orderedSegmentSquareIntegrableConversion`.

All data are `T.SegmentProductDatum.{max uF uV, uF} n` (segments `Δ_i` with blocks
`π_i`), with `letI := T.topology`.

- `exists_unitaryExponent`: if `d.HasSegmentHeads`, every block `d.blocks i` is
  essentially square-integrable (published `segmentSpecialEssentialSquareIntegrability`)
  and has a `UnitaryExponentData` for `|det|` on `GL_(deg Δ_i)`. The unitary structure
  comes from the published `glSquareIntegrableUnitarity` after removing the exponent.
- `exists_sorted`: a precedence-ordered datum of segment heads has a datum `d'` with the
  same multisegment and segment heads, chosen exponent data `u i` that are antitone in
  `i`, and `d.induced ≅ d'.induced`. Proof: `finitePermutationSorting` by adjacent
  swaps. A swap is only needed when the earlier exponent is smaller. Then the two
  segments are not linked (published `linkedSegmentHeadExponentComparison`), so the swap
  keeps precedence order (`IsPrecedenceOrdered.permute_adjacentSwap`) and the induced
  representation up to isomorphism (`adjacentUnlinkedSegmentSwap`).
- `isPrecedenceOrdered_of_antitone`: a datum of segment heads whose chosen exponents
  decrease is precedence-ordered. If `Δ_i` precedes `Δ_j` with `i < j`, then
  `linkedSegmentHeadExponentComparison` forces the exponent of `i` to be strictly smaller
  than that of `j`.
