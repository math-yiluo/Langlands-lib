# Spanning by adjacent low and high Fourier windows

This module concerns the actual compact-finite principal-series
space `PrincipalSeriesAnnihilator.KFin n χ`, with its compact Haar inner product.
It uses no additional literature premise.

`RealAdjacentWindowSpanningStatement` quantifies the rank `n`, adjacent positions
`p,p+1` lying in a three-coordinate block (`p+3≤n`), natural cutoffs `h<m`,
and complex-linear endomorphisms `P,Q` of that space. Both maps must commute
with right translation by `O(n)`. On compact points, `P` has multiplier
`lowMultiplier m j`, equal to one for `|j|<m` and zero otherwise, at position
`p`. At position `p+1`, `Q` has the complementary multiplier
`highMultiplier h j`, equal to one for `h≤|j|` and zero otherwise.
The conclusion is `range P ⊔ range Q = ⊤`.
`realAdjacentWindowSpanning` proves this proposition.

The proof uses the real-multiplier adjointness identity from
`RealBlockCompactAdjoint`. The sum of the ranges is stable under the compact
group. If a vector were outside that sum, the published
`exists_ne_zero_inner_eq_zero_kfin` theorem would supply a nonzero vector `w`
orthogonal to it. Self-adjointness implies `P w=Q w=0`: evaluate
orthogonality on `P(P w)` and `Q(Q w)` and use positivity of the inner product.
The coefficient formulas then make `w` high at position `p` with cutoff `m`,
and low at position `p+1` with cutoff `h`. Published ambient adjacent-rotation
uncertainty forces its compact restriction to vanish. Compact restriction
uniqueness contradicts that `w` is nonzero.

The helper `surjective_comp_of_range_sup` states the resulting linear-algebra
consequence. Given any complex module `E`, a surjective map `T` from this
principal series to `E` that kills the range of `P` remains surjective after
composition with `Q`. It decomposes each preimage into the two ranges.

The endomorphisms are inputs here. This module does not construct their concrete
rank-one Frobenius formulas, identify an induction-block subspace, or prove
the unrestricted two-induction-block filtration.
