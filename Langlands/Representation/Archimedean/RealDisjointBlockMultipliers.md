# Real block multipliers on disjoint coordinate pairs

Module: `Langlands.Representation.Archimedean.RealDisjointBlockMultipliers`.
Namespace: `Langlands.Archimedean.RealDisjointBlockMultipliers`.

This is internal infrastructure for the two induction block swap. It proves
commutation of block Frobenius operators on disjoint coordinate pairs. It asserts
neither that suitable Frobenius data exist nor that any multiplier is injective.
It does not prove `RealInducedSwapStatement`.

For a function `f` on `GL_n(ℝ)`, write
`Φᵖ_j f(g) = blockFourierCoefficient n p j f g`, the unnormalized left Fourier
coefficient for rotation in coordinates `p,p+1`. The selected definition
`finiteMultiplier n p D μ f` is the function

`g ↦ (2π)⁻¹ ∑_{-D ≤ j ≤ D} μ(j) Φᵖ_j f(g)`.

The window `D` is a natural number. This finite expression is defined for every
complex-valued function; its commutation theorems assume continuity of the source
so that Fourier integrals and finite sums can be interchanged.

`coefficient_congr_on_compact` and `finiteMultiplier_congr_on_compact` say that
these expressions at an orthogonal matrix depend only on the values of `f` on
`O(n)`. Every point sampled by a rotation remains in `O(n)`.

If `p+1<q` or `q+1<p`, `coefficient_finiteMultiplier` proves

`Φᑫ_k (finiteMultiplier n p D μ f)
 = finiteMultiplier n p D μ (Φᑫ_k f)`.

The proof distributes the integral over the finite sum, then uses the published
`RealBlockFourierFinite.blockFourierCoefficient_comm`. Consequently
`finiteMultiplier_comm` says that finite multipliers along the disjoint pairs
commute, for arbitrary complex sequences `μ,ν` and finite windows `D,E`. No
recurrence or symmetry condition is needed for this finite sum identity.

For `h : IsBlockFrobData n ds es p ε σ μ`,
`blockFrobMap_eq_finiteMultiplier` identifies `blockFrobMap h f` with this finite
expression on `O(n)` whenever the source coefficients along `p` vanish outside
`[-D,D]` there. The published compact formula for `blockFrobMap` and the stated
bound turn its finite support sum into precisely the displayed finite sum.
Such a uniform bound exists for every source vector.

`blockFrobMap_preserves_disjoint_bound` says that a uniform compact Fourier bound
on a disjoint pair is preserved by `blockFrobMap h`. Use the preceding finite
expression and commute its coefficient along the other pair; the resulting sum
is zero because every sampled point is compact.

Finally, `blockFrobMap_commuting_square` takes four supplied Frobenius data:

- `hp : xs → ys` along `p` with multiplier `μ`;
- `hq : xs → zs` along `q` with multiplier `ν`;
- `hq' : ys → ws` along `q` with multiplier `ν`;
- `hp' : zs → ws` along `p` with multiplier `μ`.

If the pairs are disjoint, it proves the exact equality
`blockFrobMap hq' (blockFrobMap hp f)
 = blockFrobMap hp' (blockFrobMap hq f)`.
Choose source bounds `D,E`, preserve the opposite bound through the first map on
each path, and use `finiteMultiplier_comm` to compare compact values. Both paths
land in the same supplied target standard module `ws`; published principal-series
uniqueness therefore upgrades agreement on `O(n)` to equality of the actual
functions. No rank or sign hypotheses beyond those already in the four
`IsBlockFrobData` records are suppressed.

The provenance is internal: every construction and proof is a consequence of
finite sums, the published disjoint Fourier coefficient identity, compact finite
support of right orthogonal finite functions, and the published block Frobenius
formula and compact uniqueness theorem. No external mathematical result is assumed.
