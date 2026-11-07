# A uniform geometric piece from blockwise Jacquet tensors

This internal construction generalizes the tensor transport part of
`TwoSegmentShuffle.pieceEquiv`. It uses the published uniform-refinement and
whole-Levi geometric-piece equivalences. No segment classification assertion is
added.

`UniformJacquetTensorPiece.pieceEquiv` starts with arbitrary smooth source blocks
and a minimal double-coset representative for a uniform target of block rank
`r > 0`. It assumes the actual source and target intersection refinements, that
all source-refinement sizes are divisible by `r`, and an equivalence from each
source block's normalized Jacquet module to its assigned target-factor tensor.
The target factors may have a carrier universe independent of the source blocks.
It constructs an equivalence of the actual geometric piece with the external
tensor of those target factors.

The proof first uses the whole-target piece equivalence to express the piece as
the transported refined Jacquet module. Tensor compatibility with refined
Jacquet modules and the supplied blockwise equivalences replace this module by
the nested target tensor. The flattened Levi coordinate equivalence identifies
its action with the product-coordinate action. Finally the uniform-refinement
tensor equivalence removes the Weyl transport and reindexes the nested tensor
as the specified target tensor. All smoothness, intersection, divisibility and
minimality premises are retained explicitly.
