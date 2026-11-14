# Totally singular sums of nonopposite torus row weights

Author: Worker 186. Uses Worker 350's quadratic sandwich argument.

This internal derived module works over any field `K` and any finite-dimensional
division `K`-algebra `D` with a first-kind involution `σ`. The row index `n` is
finite. The torus `i : Gm^I → O(q)` need not be injective or maximal, and the
quadratic form `q` need not be nondegenerate. No infinitude, characteristic,
centrality, type or smoothness assumption is imposed.

`torusRowWeightSum q i S` is the supremum of the full-torus row submodules
`torusRowWeightSpace q i m` for `m` in a finite set `S` of integral exponent
vectors. The spaces use the inverse-right row action already defined in
`TorusCocharacterWeightSpace` and `FiniteMatrixRowWeights`.

`finrank_torusRowWeightSum` says that its dimension over `D` is the sum of the
dimensions of its summands. The proof uses independence of the universal row
weight spaces and the dimension formula for a sum of two disjoint submodules.

`vecMul_sum_weightElement_of_mem_torusRowWeightSum` says that every row in this
submodule is fixed by `f = ∑_{m ∈ S} e_m`, where `e_m` are the universal weight
idempotents. Each selected weight space lies in the kernel of the left
`D`-linear map `x ↦ x f - x`, by the Kronecker projection rule.

Suppose no two members of `S`, including a member paired with itself, sum to
zero. Then `isTotallySingular_torusRowWeightSum` proves that the entire sum is
totally singular for `q`. The inverse universal torus point preserves the
quadratic form over the group algebra `K[ℤ^I]`. Its defect's constant
coefficient lies in the quadratic kernel. Sandwiching this coefficient by
`f` and its involution kills every pair of opposite exponents, and gives
`f Q τ(f)` in the quadratic kernel, with `Q` the chosen matrix representing
`q`. Worker 350's `quadraticValue_eq_zero_of_vecMul_eq` then makes every row
fixed by `f` singular.

Finally `sum_finrank_torusRowWeightSpace_le_quadraticWittIndex` bounds the
sum of these multiplicities by the Witt index. It combines the dimension
identity and the published bound for every totally singular subspace.
This strengthens the cardinality argument in `QuadraticTorusWittBound` to
the full sum of the dimensions; it does not prove multiplicity one,
opposite-weight duality, or the maximal-split-torus weight theorem.
