# Embedding weight spaces of actual Harris cocharacters

This internal construction uses the published complex points and matrix coordinates of the rational Harris similitude group, the published cocharacter evaluation maps, and the existing common inverse-weight submodule. All central-simple unitary input, CM section and signature charts remain explicit. The embeddings index both members of each CM pair.

`complexEmbeddingPointUnit` constructs the invertible matrix at each embedding from an actual group point. Its value is the existing matrix coordinate and its inverse is the coordinate of the inverse group point. This follows by lifting the coordinate monoid homomorphism, whose domain is already a group, to matrix units; invertibility is not an additional hypothesis.

`complexEmbeddingWeightSpace` is the submodule of vectors on which every matrix in an actual point family indexed by complex units acts through the inverse of that unit. `complexEmbeddingWeightSpaceConjEquiv` acts on a column vector by left multiplication with the matrix of a fixed group point. Multiplicativity of the matrix coordinates identifies the conjugated family with matrix-unit conjugation, so the published conjugation equivalence restricts to these submodules. Its finite-rank equality holds at every CM embedding.

`directCocharacterWeightSpace` and `complexCocharacterWeightSpace` specialize this construction to evaluation of actual scheme cocharacters in the direct and iterated complex base-change models. The canonical group-scheme comparison gives identical submodules. At the first-factor Kottwitz cocharacter, the submodule is the already constructed `kottwitzEmbeddingWeightSpace`; consequently its rank, and that of every pointwise conjugate family, equals `realHodgeFunction`.

The provenance is composition of the published point-coordinate, conjugation and Kottwitz-weight constructions, with no further literature theorem. This module does not assert Galois invariance, classification of all cocharacters by weights, or equality of a cocharacter stabilizer with a reflex-field stabilizer. Those require further comparison results.
