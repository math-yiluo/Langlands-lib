# Unitarity of `⟨a(n,1)^ρ⟩`

Author: Worker 5121. Module `Langlands.Representation.Classification.TadicBlockSteinberg`,
namespace `Langlands.Classification.TadicBlockSteinberg`. Helper module of the proof of
`Langlands.Classification.TadicBlockReductionFromInputs`.

## Results

- `downDatum ρ₀ A n`: the segment-product datum of the one-element segments
  `{ν^(n-1-i) ρ₀}`, `i < n`, in decreasing order, with blocks the twists of a supercuspidal
  representative `A` of `ρ₀` (rank-cast to the singleton-segment degree).
  `downDatumInducedIso` identifies its product with the published decreasing induction
  `segmentInducedDown A n` (`normalizedProductRankCastIso`); `downDatum_hasSegmentSocles`
  (published `singletonSegment_isSegmentSocle`); `downDatum_isPrecedenceOrdered` (a later
  segment has a smaller exponent, by `cuspidalDatum_twist_injective`);
  `downDatum_multisegment`: for `ρ₀` the beginning of `Δ[n]^ρ`, its multisegment is
  `a(n,1)^ρ = tadicMultisegment ρ n 1` (both multisets are duplicate-free with the same
  members, matched by `i ↦ n - 1 - i`).
- `isZelevinskySocle_tadicSegmentHead`: the published special head `tadicSegmentHead ρ hn`
  of the centered segment `Δ[n]^ρ` is a Zelevinsky socle of `a(n,1)^ρ`, because it is the
  irreducible socle of the decreasing induction (published
  `IsSegmentHead.isIrreducibleSocle_down`).
- `isUnitarizable_of_isZelevinskySocle_one`: for unitary `ρ` and `n > 0`, every Zelevinsky
  socle `σ` of `a(n,1)^ρ` is unitarizable. Its rank is `n · rank ρ`; it is isomorphic to the
  special head (published `nonempty_iso_of_isZelevinskySocle`), which is irreducible,
  unitarizable and square-integrable by the published `tadicSpehDatum_isDiscreteSeries`.

## Sources

Tadić 1986 (`tadic-1986-unitary`), §2.14 and §3.2 (pp.352–353): `⟨Δ^(ρ)⟩` and
`⟨a(n,1)^(ρ)⟩` are unitarizable for `ρ ∈ C^u`; here the unitarity comes from the published
square-integrability of the centered special representation.
