# Refining exactly one ordered block by one additional cut

`blockShapeSingleCut` sends an internal coordinate cut of a block to its
global coordinate cut. The adjacent coordinates belong to the same original
block, so the global cut is absent from the original cut set.

Inserting it changes the cut-count weight by one on the coordinates after
the cut. In every other coarse block this is a constant change. In the
split block the comparisons of the new weights are exactly the comparisons
of the two-block weights. Therefore the intersection of the refined
radical with the original Levi is the image of the two-block radical in
the specified block under `blockShapeSingleEmbedding`. The equality is
proved on the original invertible matrices over any commutative ring.

This is the matrix comparison for the nested unipotent integrals in the
Levi-cuspidality step of Langlands's proof of Proposition 2, printed
pp. 204–205 (Corvallis Part I, PDF pp. 199–200). The registered source is
`langlands-1979-notion-automorphic-representation`, SHA-256
`3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`.
