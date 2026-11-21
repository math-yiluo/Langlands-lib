# Infinite Whittaker slices for GL₁

`rankOneWhittakerSlice` constructs the `InfiniteWhittakerSlice.ModelData` of an actual cuspidal spectral presentation of GL₁. It retains the irreducibility and admissibility hypotheses on the finite components and both universes of the presentation. The construction applies to every adelic additive character because the unipotent group is trivial.

Every rank-one adelic matrix is a scalar matrix. The central-character transformation law therefore determines each cusp function by its value at the identity. Evaluation there is injective on the cuspidal space and on each of its chosen nonzero place subspaces. The proof rescales a vector in each subspace to have value one. The local coefficient map multiplies the resulting evaluation functional by the restriction of a cusp function normalized at the identity.

Replacing a single tensor component scales the tensor by its evaluation relative to the corresponding normalized vector. Replacing its group coordinate factors the adelic point into the element at that place and the point with identity in that coordinate. The central-character law and `RealRankZero.cuspWhittaker_rankZero` give the required slice identity with all the other coordinates fixed.

This is an internal derivation of the rank-one case of `InfiniteWhittakerSliceModelStatement`. The proof uses the Library's `existsUnique_hasCentralCharacter`, `cuspFunction_scalarPoint_mul`, and `cuspWhittaker_rankZero`.
