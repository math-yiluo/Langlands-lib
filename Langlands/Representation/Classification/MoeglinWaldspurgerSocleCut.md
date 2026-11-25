# The socle cut

Module `Langlands.Representation.Classification.MoeglinWaldspurgerSocleCut`.

`socleCut_embeds`: let `Δ` be a segment of length `k + 2`, `A` a supercuspidal representative of
its base, `Z` a segment socle of `Δ` and `Z'` a segment socle of the segment
`[ν^1 base, …]` of length `k + 1`. Then `Z` embeds, up to rank transport, into `A × Z'`.

Proof. By the published `isSegmentSocle_iff`, `Z` is the strong socle of the increasing
induction `i(A, νA, …)` and `Z'` that of `i(νA, …)` (representative `twistRep 1 A`). The
published `SegmentHeadSupport.nonempty_iso_segmentInduced_split` writes the former as the rank
transport of `ν^0 A × i(νA, …)`. Hence `σ = ν^0 A × Z'` embeds into the increasing induction of
`Δ`; `σ` is nonzero of finite length, so the published
`IsIrreducibleSocle.finiteLengthSubobjectEmbedding` embeds `Z` into `σ`. Finally the lifted
`ν^0 A` is isomorphic to `A` (`castIso_universeLift_segmentFactor_zero`). Helpers transport
injectivity, nontriviality and finite length along `Derivative.generalLinearRankCast`.
