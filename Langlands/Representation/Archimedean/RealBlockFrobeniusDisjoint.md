# Frobenius maps on disjoint blocks commute

Module `Langlands.Representation.Archimedean.RealBlockFrobeniusDisjoint`.
The helper namespace is `Langlands.Archimedean.RealBlockFrobeniusDisjoint`.

This is derived internal infrastructure for the two-induced-block filtration.
It uses the Library's block Frobenius maps, their compact-group multiplier
formula, finite Fourier support, and commutation of disjoint Fourier
coefficients. It has no external literature source.

Write `K(ds)` for the actual `O(n)`-finite functions in
`realStandardModule n ds`, and `Φᵖⱼ` for
`blockFourierCoefficient n p j`. The Frobenius map with multiplier `μ`
at position `p` is denoted `Bᵖ_μ`; it is defined from supplied
`RealBlockFrobeniusMap.IsBlockFrobData`.

`RealDisjointBlockFrobeniusCommutationStatement : Prop` states that the
following square commutes. Its data are arbitrary rank `n`, positions `p,q`,
lists `ds,es,fs,gs`, parities, signs, multipliers `μ,ν`, and four valid
`IsBlockFrobData` instances:

| Route | First map | Second map |
| --- | --- | --- |
| Through `es` | `Bᵖ_μ : K(ds) → K(es)` | `Bᑫ_ν : K(es) → K(gs)` |
| Through `fs` | `Bᑫ_ν : K(ds) → K(fs)` | `Bᵖ_μ : K(fs) → K(gs)` |

Under `p + 1 < q` or `q + 1 < p`, the two composite complex linear maps
are equal. The parity at each position is shared by the two routes; their
sign parameters may differ. There is no recurrence, nonvanishing or
invertibility hypothesis in addition to the four valid data instances.
`realDisjointBlockFrobeniusCommutation` proves this proposition.

The implementation first proves `blockFourierCoefficient_congr_on_compact`:
the coefficient at `k ∈ O(n)` depends only on values on `O(n)`, because
every point `r_q(θ)k` in the defining integral is in `O(n)`.
It then proves `blockFourierCoefficient_frobFun_disjoint`, for arbitrary
Frobenius exponents and signs satisfying the existing sign covariance:

```text
Φᑫᵢ(Bᵖ_μ f)(k) = (2π)⁻¹ Σⱼ μ(j) Φᵖⱼ(Φᑫᵢ f)(k),  k ∈ O(n).
```

Here the sum is the Lean `finsum`. A uniform finite bound on the `p` modes
of `f` makes the Frobenius function on the entire `q` orbit a finite sum.
The defining integral distributes over that sum; the Library theorem
`blockFourierCoefficient_comm` exchanges the two disjoint coefficients.
The same uniform bound shows that the resulting summands vanish outside
the finite interval, justifying the `finsum`. The map version is
`blockFourierCoefficient_blockFrobMap_disjoint`.

For `blockFrobMap_disjoint_comm`, compute the `p` coefficients of both
composites on `O(n)`. Apply the disjoint formula to the second map on the
route through `es`, and the direct multiplier formula to the second map
on the route through `fs`. On each compact `q` orbit, the `p` coefficient
after the first `p` map is `μ(i) Φᵖᵢ f`; take this scalar through the
`q` integral and the finite-support sum. Both results coincide.
The Library's `eq_of_blockFourierCoefficient_eq` then gives equality of
the actual functions on all of `GL_n(ℝ)`, since both outputs belong to
the same standard module `K(gs)`. Linear-map extensionality gives the
stated composite equality.

This unit supplies an interchange rule once the four map data have been
constructed. It does not construct the GL₄ block-exchange maps, prove a
landing theorem, or establish the full induced-pair filtration.
