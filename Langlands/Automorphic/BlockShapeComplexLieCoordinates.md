# The block Lie inclusion in complex archimedean coordinates

`complexLieProductMatrixCoordinates_blockShapeInclusion` compares the differential of the genuine block embedding with its complex matrix coordinates. First insert a matrix of the given block rank at each archimedean matrix factor and put zero in the other blocks. Then apply the actual full block diagonal inclusion. On simple tensors, entrywise place evaluation, scalar extension and conjugation commute with this matrix inclusion. Tensor induction gives the comparison on the complexified Lie algebra, and the universal property gives the comparison on enveloping algebras.

`blockMatrixFactorCenterInclusion` maps the enveloping centre of an individual block, taken over all archimedean matrix factors, into the centre of the full matrix Levi. Split a full Levi direction into its component in the block and a direction vanishing on that block. The component commutes with the central element in the block. The remaining direction commutes with every Lie generator from that block and hence with its entire enveloping algebra.

This derived comparison connects the actual Lie action on the slices to the block centre projection in the Levi restriction argument of Langlands, *On the notion of an automorphic representation* (1979), Lemma 4, printed p. 204.
