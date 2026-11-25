# Standard block sums and rank inclusions

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
published canonical realization for every algebraic `PadicField p`.
They choose the topology locally, with no additional realization premise.

The project dependencies are the `Basic` and `Padic` constructions. Their
pairs were checked for their dependency closure, and they build with Lake.
