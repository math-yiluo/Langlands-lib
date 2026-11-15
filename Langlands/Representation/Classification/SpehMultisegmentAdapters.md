# Actual Speh quotients and rectangular multisegments

These internal adapters use the published segment classification of actual
essentially square-integrable representations. A supplied discrete-series action
therefore has a strong segment-head description. Keeping that same action and
carrier, the centered Speh induction is the segment-head product of the real
twists of this segment. Real twist-freeness makes its decreasing sequence
precedence-ordered, and published real-twist compatibility identifies every block
as a segment head. The given Speh quotient is consequently a weak Langlands
quotient for this segment-product datum.

Twisting the original segment's beginning by its midpoint yields a centered
cuspidal base. The original segment is precisely the centered segment for that
base; the published reversed-index identity for centered rectangles then
identifies the multisegment of the constructed datum with `tadicMultisegment`.
No unitarizability of the Speh quotient and no Aubert comparison are used. The
adapters cover arbitrary independent field and carrier universes and retain
all actual representations. They are derived interfaces for the neighboring
Speh proof, rather than a new classification assertion.

## Declarations

The segment-product construction and its induction, ordering and segment-head
lemmas are reused from `SpehSegmentParameters`. This module adds the centered
rectangular label and quotient adapters listed below.

- `tadicCenteredSegment_midpoint`: let ρ be the base of a segment Δ twisted by
  `(Δ.length − 1)/2`. The segment of length `Δ.length` centered at ρ with
  shift 0 is Δ itself.
- `SpehDatum.segmentProductDatum d Δ h`: for a segment Δ of degree `d.rank`,
  the segment-product datum with `d.length` blocks. Block `i` is the twist of Δ
  by `d.exponent i`, carrying the segment factor of `d.delta` at that exponent.
- `SpehDatum.segmentProductDatum_induced`: its induced representation is
  `d.centeredInduced`.
- `SpehDatum.segmentProductDatum_isPrecedenceOrdered`: the datum is
  precedence-ordered, by real-twist injectivity.
- `SpehDatum.segmentProductDatum_hasSegmentHeads`: if `d.delta` is a segment
  head for Δ, then every block is a segment head for its segment, by published
  real-twist compatibility.
- `SpehDatum.segmentProductDatum_centered_multisegment`: its multisegment is
  `tadicMultisegment` of the centered base, with `d.length` rows of length
  `Δ.length`.
- `SpehDatum.isLanglandsQuotient_segmentProductDatum`: a Speh quotient `S`
  with `d.IsSpeh S` is a weak Langlands quotient of this datum.
- `SpehDatum.exists_segmentHead`: for a discrete-series datum, the published
  segment classification of essentially square-integrable representations
  provides a segment Δ of degree `d.rank` with `d.delta` a segment head for Δ.
