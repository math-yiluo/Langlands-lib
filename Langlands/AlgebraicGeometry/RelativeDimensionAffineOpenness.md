# Affine relative fibre dimension and open source charts

This helper module in Worker 105's proof of relative-dimension sublevel
openness first restricts an open
source embedding to an actual point fibre. Open embeddings preserve local
topological dimension, so this restriction identifies the two local fibre
dimensions.

For a finite-type map of arbitrary commutative algebras, the constructed
`FiberDimensionLocalChart` gives an open source neighbourhood containing
each point. Its every original-base fibre has total dimension bounded by
the local dimension at the original chosen point. At any lifted point the
local dimension is at most that total dimension. The open-source
comparison then proves that this neighbourhood stays within the same
natural sublevel.

The companion module `RelativeDimensionSublevelOpennessProof` transfers
this affine assertion to arbitrary locally finite-type scheme morphisms.
This argument supplies an internal prerequisite toward Conrad
Theorem 3.4(2), rather than that theorem's filtered-descent conclusion.
Retrocompactness and geometric-connectedness constructibility remain
separate obligations.
