# Ball norms and nearest vertices in the norm model of the building

This is an internal construction for the covering and the forward nerve implication in
[`DrinfeldCoveringStatement.lean`](DrinfeldCoveringStatement.lean). It works directly with
`VectorNorm`, `NormClass` and the multiplicative Goldman–Iwahori distance; it does not
assume the existence of adapted bases or use an apartment comparison. The construction
and quantitative bounds below describe the implementation, not additional assertions
attributed to Harris.

## Discreteness and rounding

`VectorNorm.IsMaxBelowOne ϖ` says that `0 < ‖ϖ‖ < 1` and that every scalar norm
strictly below 1 is at most `‖ϖ‖`. For a proper nontrivially normed ultrametric field,
`exists_isMaxBelowOne` obtains such a scalar by maximizing the values below 1 in a
compact annulus `‖c‖ ≤ ‖t‖ ≤ 1`, where `0 < ‖c‖ < 1`. There are only finitely many
values in that annulus: the norm is constant on the open ball of radius `‖t‖`
centered at `t` and these balls have a finite subcover. With `q = ‖ϖ‖⁻¹`,
`IsMaxBelowOne.exists_norm_eq_zpow` proves that the nonzero scalar norms are powers
of `q`, by reducing to the interval `[1,q)` and using maximality of `‖ϖ‖`.
The number `q` here is determined by the given norm, not by a choice of normalization.

`VectorNorm.up q r` rounds a positive real `r` up to the least integral power
of `q` when `q > 1` (and is zero outside this range of parameters). Its
characterizing inequalities are `r ≤ up q r < q r` with `up q r ∈ q^ℤ`.
Rounding is monotone on positive inputs and commutes with multiplying by a
power of `q`.

## Ball norms

Given an ultrametric norm `ν` and `s > 0`, `VectorNorm.ballNorm` is the norm
`β_s(a) = up q (ν(a)/s)`. Its unit ball is `{a | ν(a) ≤ s}`. Scalar homogeneity
follows from the power description of scalar norms, and its ultrametric inequality
follows from monotonicity of rounding. It is a lattice norm in the sense of
`VectorNorm.IsLatticeNorm` (its values are scalar norms).

The rounding bounds give `distRatio ν β_s ≤ q`. Conversely, on a nonzero vector
space, if `μ` is a lattice norm and `distRatio ν μ < q`, then `μ = β_R` for
`R = (ratioSup ν μ).toReal`. Indeed the two ratio suprema are positive and finite
under this distance bound. For `a ≠ 0`, they imply `ν(a)/R ≤ μ(a) < q ν(a)/R`.
Uniqueness of rounding gives the equality. Changing `s` by a factor in `q^ℤ`
changes `β_s` by homothety, so one can represent every such vertex by a radius
in `[1,q)`.

## Finiteness, nearest vertices, and chains

For any `c > 0`, vectors with pairwise distinct values in `[c,qc)` are linearly
independent (for a finite family). Nonzero scalar multiples of the distinct
values cannot coincide: their ratios would be nontrivial powers of `q` in
`(1/q,q)`. Hence a nontrivial relation would have a unique term of maximal
norm, which cannot cancel in an ultrametric norm. This proves finiteness of
the values in `[1,q)` in finite dimension. Rounding produces the same ball norm
at `s ≤ s'` when no value lies in `(s,s']`: a change in the rounded value would
produce such a value after rescaling by a power of the uniformizer. Thus,
for fixed `ν`, the finitely many breakpoints in `[1,q)` together with 1 suffice
for the classes of all vertices of distance strictly less than `q`.

For `N = dim_F V > 0`, set `λ = exp(log q / N)`. There is some `v₀ = ν(a₀) > 0`
with no value in `(v₀, λ v₀)`: otherwise one can successively pick `N+1` distinct
values in `[v₀, q v₀)` using `λ^N = q`, contradicting linear independence.
After rescaling by any power of the uniformizer the same gap persists. It improves
the upper rounding bound for `β_{v₀}`, giving `distRatio ν β_{v₀} ≤ q/λ < q`.
So there exists a vertex strictly within distance `q`. A minimum over the finite
nonempty set of such vertices is a global minimum. In particular the stars
cover the norm classes, and membership in a star bounds the distance to its
vertex by `q/λ`.

`NormClass.isFacet_of_distRatio_lt` takes a nonempty finite set of vertices each
at distance strictly less than `q` from a common point. Choose a representative
`ν` of that point, and represent the vertices by `β_s` with `1 ≤ s < q` as above.
In decreasing order of `s` these norms are increasing, with the last at most
`q` times the first; multiplication by any `‖t‖ < 1` therefore bounds the last
by the first. This is precisely `VectorNorm.IsLatticeChain`, with range of
classes the original set. Finally the module proves the multiplicative triangle
inequality for `distRatio` (also on classes) by bounding each ratio supremum
through an intermediate norm.
