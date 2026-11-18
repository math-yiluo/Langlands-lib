# Coordinates of a split lattice-chain filtration

Supporting lemmas for BK93 §1.1 and `RadicalFiltrationStatement`, derived
from `SplittingBasis` and the published `LatticeChain` definitions.
Worker 408 supplied the elementary endomorphism and entry-filtration
proofs. Worker 628 generalized the entry-filtration proofs to arbitrary
vector spaces.

`elementaryEnd β k l t` sends a vector to its \(l\)-th coordinate times
`t β_k`. The scalar `entry β x k l` is the \(k\)-th coordinate of
`x (β l)`. The finite double sum of elementary endomorphisms with these
entries is `x`. In `elementaryEnd_mul`, composable elementary maps with
a matching intermediate index multiply their coefficients. Multiplication
on either side by diagonal elementary projections isolates the corresponding
entry. The trace identity uses `LinearMap.trace_smulRight` for a rank-one map.

If \(\beta\) splits the chain and `t ≠ 0`, `elementaryEnd_mem_iff`
identifies membership in the \(n\)-th filtration module with
`n + index β_l ≤ e ordOf t + index β_k`. Necessity tests on
`β l` at its maximal lattice index using
`LatticeChain.mem_lattice_index`. Sufficiency projects a lattice
vector onto its \(l\)-th coordinate by `LatticeChain.Splits`
and applies `LatticeChain.mem_iff_le_index`, `LatticeChain.index_smul`
and `ordOf_mul`. Diagonal projections therefore belong to
`LatticeChain.endFiltration 0`. Two uses of the published
`LatticeChain.mul_mem_endFiltration` bound each nonzero entry of an
arbitrary filtration element in `le_of_mem_endFiltration`.
The field and vector space universes are independent.
[Splitting basis](SplittingBasis.md)
