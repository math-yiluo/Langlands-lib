# A common point of the vertex stars of a facet

This module constructs a barycenter for a chain of lattice norms in the Library's
norm model. It is an internal construction for the reverse nerve implication of
[`DrinfeldCoveringStatement.lean`](DrinfeldCoveringStatement.lean). The argument
uses only discreteness of the scalar norm and the order bounds on chains, not
coordinates in an apartment or an identification with a barycentric subdivision.

## Chain data and the norm

Let `ϖ` be as in [`DrinfeldNearestVertex.lean`](DrinfeldNearestVertex.lean), with
`q = ‖ϖ‖⁻¹ > 1`. `IsChainData ϖ μ`, for `μ : Fin m → VectorNorm F V`, says
that the norms are lattice norms, pointwise increasing with the index, and
satisfy `μ_i ≤ q μ_j` for all `i,j`. For `m > 0`, `VectorNorm.barycenter` is
the norm

`ν(a) = (∏ᵢ μ_i(a))^(1/m)`.

The key to the ultrametric inequality is `IsChainData.comparable`: for any pair
of vectors `a,b`, the two lists of values are comparable componentwise. In fact,
if `μ_i(a) < μ_i(b)`, discreteness gives `q μ_i(a) ≤ μ_i(b)`. For `j ≥ i`, use
`μ_j(a) ≤ q μ_i(a) ≤ μ_i(b) ≤ μ_j(b)`; for `j ≤ i`, use
`q μ_j(a) ≤ q μ_i(a) ≤ μ_i(b) ≤ q μ_j(b)`. Thus all componentwise ultrametric
bounds for `a+b` use the same dominating list, and the product and root preserve
that bound. Positivity and scalar homogeneity follow directly from those of
the `μ_i`.

## Exact minimum distance

`distRatio_barycenter_le` bounds the distance from `ν` to each `μ_j` by
`(q^(m−1))^(1/m)`. In bounding `ν/μ_j`, each factor `μ_i/μ_j` contributes a
factor at most `q` if `j < i`, at most 1 otherwise. In bounding `μ_j/ν`, a
factor `μ_j/μ_i` contributes at most `q` if `i < j`, at most 1 otherwise.
In the product of the two bounds there are `m−1` factors of `q` before the root.

If the classes of the `μ_i` are distinct and `V` is nontrivial,
`le_distRatio_barycenter` gives the matching lower bound to **every** lattice
norm `μ'`. For each `j > 0` choose `b_j` on which `μ_{j−1}` and `μ_j` differ.
At this vector the chain values must jump from `μ_0(b_j)` to `q μ_0(b_j)`
exactly at `j`, since the nonzero lattice values are powers of `q` and the
whole chain is within a factor `q`. For `j = 0` choose `b_0 ≠ 0` on which the
chain is constant. For `m > 1` there is such a vector because otherwise the
last norm would equal `q μ_0` everywhere, contrary to distinctness of classes;
for `m = 1` any nonzero vector suffices.

The `m` values `(ν(b_j)/μ'(b_j))^m` are then powers of `q` with exponents
congruent to `−j` modulo `m`. These give `m` distinct integers, so the spread
between the maximum and minimum exponents is at least `m−1`. Taking the ratio
of the corresponding values of `ν/μ'` and bounding this by `distRatio ν μ'`
yields the lower bound.

## Application to a facet

`IsLatticeChain.exists_strict` shortens a published `IsLatticeChain` to the
first occurrences of the classes, preserving their order and range. The
original chain bound with `t = ϖ` gives the pairwise factor bound for the
shortened chain. For any `IsFacet S`, apply this shortening to its witness
and take the class of the constructed norm. The upper and lower distance
bounds prove that each vertex of `S` is a nearest vertex to that class, giving
`NormClass.exists_mem_vertexStar_of_isFacet`. Lifting this class to an analytic
point is a separate step, not part of this module.
