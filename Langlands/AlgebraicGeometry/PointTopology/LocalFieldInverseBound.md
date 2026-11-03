# A compact set containing every element or its inverse

This helper module supplies the only topological input on the coefficient field
used by the proof of
`Langlands.AlgebraicGeometry.PointTopology.LocalFieldProperPointProperties`.
Throughout, `K` is a field with a topology making it an
`IsTopologicalDivisionRing`; the two results also assume `T2Space K`,
`LocallyCompactSpace K` and `¬ DiscreteTopology K`. No norm or valuation is used.

## `exists_ne_zero_tendsto_pow_zero`

There is `t : K` with `t ≠ 0` and `t ^ n → 0` as `n → ∞`.

Proof as implemented. Choose a compact neighbourhood `V` of `0`, and (the space is
regular, being a topological group) a closed neighbourhood `F` of `0` with
`F ⊆ V` and `1 ∉ F`. The tube lemma
(`IsCompact.eventually_forall_of_forall_eventually`) applied to multiplication
near `{0} × V` gives a neighbourhood `W` of `0` with `w * v ∈ F` for all `w ∈ W`,
`v ∈ V`. Since `K` is not discrete, `{0}` is not open, so `V ∩ W` contains some
`t ≠ 0`. By induction `t ^ (n + 1) ∈ V` and `t ^ (n + 2) ∈ F` for all `n`.
The powers stay in the compact set `V`, so by
`IsCompact.tendsto_nhds_of_unique_mapClusterPt` it suffices that every cluster point
`b` of the sequence is `0`. If `b ≠ 0`, continuity of `(x, y) ↦ x * y⁻¹` at
`(b, b)` gives a neighbourhood `N` of `b` with `x * y⁻¹ ∉ F` for `x, y ∈ N`
(because `Fᶜ` is a neighbourhood of `1`). Since `b` is a cluster point there are
indices `n` and `m ≥ n + 2` with `t ^ n, t ^ m ∈ N`; then
`t ^ (m - n) = t ^ m * (t ^ n)⁻¹ ∉ F`, contradicting `t ^ (m - n) ∈ F`.

## `exists_isCompact_mem_or_inv_mem`

There is a compact `C ⊆ K` such that every `x : K` satisfies `x ∈ C` or
`x⁻¹ ∈ C`.

Proof as implemented. Take `t` as above and a compact neighbourhood `V` of `0`.
Put `A = V ∩ t · (interior V)ᶜ`; it is compact (closed in `V`, because
multiplication by `t` is a homeomorphism, `Homeomorph.mulLeft₀`) and does not
contain `0`, so `A⁻¹` is compact (inversion is continuous on `A`). The set
`T = {0} ∪ {t ^ (n + 1)}` is compact because the sequence converges
(`Filter.Tendsto.isCompact_insert_range`). Let `C = V ∪ T * A⁻¹`, compact by
`IsCompact.mul`. If `x ∉ V`, since `t ^ n * x → 0` there is a least `k` with
`t ^ k * x ∈ V`; then `k = j + 1` and `t ^ j * x ∉ V`, so
`u = t ^ k * x = t * (t ^ j * x) ∈ A`, and `x⁻¹ = t ^ k * u⁻¹ ∈ T * A⁻¹`.

This is a standard argument; it is internal to the proof route chosen for the
target and is not taken from Conrad's paper, whose Proposition 4.4 instead
reduces to projective space via Chow's lemma.
