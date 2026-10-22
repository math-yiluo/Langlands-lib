# Standard block sums and rank inclusions

Author: Worker 6.

For every commutative ring and natural ranks `n,m`, `blockSum` maps two actual
general linear matrices to `diag(g,h)` in rank `n+m`. The construction first
uses Mathlib's `Matrix.fromBlocks` on the index sum, with zero off-diagonal
blocks. Its inverse is the block matrix of the two inverses. Both unit
identities and multiplication follow from `Matrix.fromBlocks_multiply`.
The identity follows from `Matrix.fromBlocks_one`. The sum index is then
relabelled by the standard `finSumFinEquiv`.

The four entry lemmas describe each diagonal block and the two zero blocks
using `Fin.castAdd` and `Fin.natAdd`. `rankInclusion m` sets the second block
equal to the identity. It is a homomorphism, and injectivity is proved by
reading back the first block. Zero ranks are allowed; no positivity or
nontrivial coefficient-ring assumption is needed.

With any coefficient topology, both maps are continuous for the actual
matrix-unit topologies. The proof checks the matrix and inverse components
using `Units.continuous_iff`. Every entry is a coordinate projection of one
input (or its inverse), or a constant zero. Continuous reindexing then
transports the map to the standard total rank. No continuity of the ring
operations is needed for these particular maps.

This is internal matrix infrastructure derived from the standard ordered
block convention and the proved maps in `Basic`, with Mathlib's block matrix
identities. It supplies no conductor-specific stabilizer or integral
reduction map. `TopologicalData.blockSum` and `TopologicalData.rankInclusion`
instantiate these exact continuous homomorphisms for every supplied p-adic
field topology. `canonicalBlockSum` and `canonicalRankInclusion` use the
accepted canonical realization for every algebraic `PadicField p`.
They choose the topology locally, with no additional realization premise.

The project dependencies are the `Basic` and `Padic` constructions in
`cd1132db-8cab-4cab-bd28-0c6164b44dbe` version 1, independently accepted and
published at commit `843c574c920aa9926ab56adf662c74b3cd4ed0e1`, effective snapshot
`42106411fcd47bace4b6e12d64b234b7564303775ee7b633bd3341e60208dd4b`.
Final review receipt `7c88f2621a5047a9a85fe9ef375a8ed0` confirms the unchanged
reviewed pairs, their current dependency closure and successful final Lake validation.
