# Actual determinant duality from finite free frames

This internal unit compares actual chosen determinant lines under
internal module duality on a supplied fixed finite-index frame cover.
For a module sheaf `M` with actual frames `e` on a cover `T i`, all
indexed by one finite type, `dualFrames` applies the actual
`dualLocalFreeIso` on each chart.

The theorem `dualFrames_matrix` says that the dual-frame transition
matrix from chart `j` to chart `i` is the transpose of the original
transition matrix in the reverse direction. The proof identifies
coordinates in the dual frame with actual evaluation on the original
basis. On the second chart these evaluations are precisely the
coordinates of the original reverse transition. This argument uses
the actual internal dual sheaf and its section evaluation pairing.

It follows that `dualFrames_unit` and `dualFrames_cocycle` invert the
actual determinant transition units and cocycle. The isomorphism
`dualFramesTensorIso` consequently makes the two actual frame
determinant lines tensor inverses: multiply their cocycles, identify
the product with the constant unit cocycle, and use the actual
structure-module comparison.

The generic construction `tensorInverseDualIso` identifies any supplied
tensor inverse `N` of an actual line `L` with its actual internal dual.
It inserts the dual evaluation inverse and uses the actual tensor
associator, the supplied inverse pairing and the unit isomorphisms.
All morphisms in this construction are isomorphisms.

For supplied finite local basis witnesses for `M` and `dual M`,
`finiteDeterminantDualIsoOfFrames` gives an actual line-bundle
isomorphism

`finiteLocallyFreeDeterminant hM ≅
  (finiteLocallyFreeDeterminant hD).dual`.

The proof compares the two frame determinant presentations with the
existing chosen actual determinants and transports the frame tensor
inverse comparison through actual line-bundle duality.

The provenance is internal finite-frame duality and sheaf tensor
algebra. The input fixed-index cover is retained. The unit neither
asserts a constant-rank cover exists globally for every finite locally
free sheaf nor makes an ampleness claim.
