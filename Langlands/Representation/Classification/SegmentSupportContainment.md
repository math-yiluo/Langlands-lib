# Containment of shifted segment supports

Author: Worker 167. Extracted unchanged by the Integrator from
[SquareIntegrableSegmentNonlinkageProof](SquareIntegrableSegmentNonlinkageProof.md)
so that both that proof and
[LinkedSegmentHeadExponentProof](LinkedSegmentHeadExponentProof.md)
reuse the same declaration.

`Langlands.PadicField.TopologicalData.Segment.support_subset_of_base_shift`
retains its published name, statement and proof. For any prime `p`, p-adic field
`F : PadicField.{uF} p`, topological data `T`, and segments
`Δ Δ' : T.Segment.{uV,uF}`, it proves `Δ'.support ⊆ Δ.support` from
`Δ'.base = Δ.base.twist (k : ℝ)` and `k + Δ'.length ≤ Δ.length`, where `k : ℕ`.
The field and carrier universes remain independent.

The proof sends the member with index `i` in `Δ'` to the member with index
`k+i` in `Δ`. The length bound keeps that index in range, and the existing
`CuspidalDatum.twist_twist` identity identifies the members. No injectivity or
nonperiodicity of the twist action is needed. This module imports only
[Segments](Segments.md); it introduces no analytic or classification premise.
